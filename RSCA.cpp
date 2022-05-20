//

#include <iostream>
#include <vector>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <string>

// Graph demands
#define INF 2147483647
#define MAX_NODE 14
#define K_LIMIT 3
// Network demands
#define BANDWIDTH 4000
#define FSPACING 12.5
#define MAX_SF 8

enum e_sort_order
{
    none        = 0,
    ascending   = 1,
    descending  = 2,
    max_sort
};

enum policy_type
{
    none_selected    = 0,
    CCP     = 1,
    FCAP    = 2,
    max_pol
};

struct slot
{
    // 0 = Code free,
    // x > 0 = x shows which connection is using the code
    // -1 = Code unavailable, child or parent has an allocated code
    int v_tree[MAX_SF*2 - 1] = {0};

    int available_codes = MAX_SF*2 - 1;
    
    void assign_code(int index, int code)
    {
        // assign code
        v_tree[index] = code;
        available_codes--;
        
        if(code > 0)
        {
            disable_parent(index);
            disable_children(index);
        }
    }

    // This function retrieves the index of the code that was assigned by a connection
    int get_index(const int& con) const
    {
        for(int i = 0; i < MAX_SF*2-1; ++i)
        {
            if(v_tree[i] == con+1) return i;
        }
        return -1;
    }
    
    void disable_children(int current_index)
    {
        int left_child = current_index*2 + 1;
        int right_child = current_index*2 + 2;

        if (left_child >= 0 && left_child < MAX_SF*2-1)
        {
            v_tree[left_child] = -1;
            available_codes--;
            disable_children(left_child);
        }

        if (right_child >= 0 && right_child < MAX_SF*2-1)
        {
            v_tree[right_child] = -1;
            available_codes--;
            disable_children(right_child);
        }
    }
    void disable_parent(int current_index)
    {
        int parent_index;
        bool is_right_child;
        if(current_index % 2 == 0)
            is_right_child = true;
        else
            is_right_child = false;

        if(is_right_child)
            parent_index = (current_index-2)/2;
        else
            parent_index = (current_index-1)/2;

        if (parent_index >= 0 && parent_index < MAX_SF*2-1)
        {
            v_tree[parent_index] = -1;
            available_codes--;
            disable_parent(parent_index);
        }
    }
};

struct link
{
    slot slot[static_cast<int>(BANDWIDTH/FSPACING)];
};

struct vertex
{
    int source;
    int dest;
    int cost;
    bool confidential = false;
};

struct demand
{
    char policy;
    char sorting;
    std::string graph_file;
    std::string connections_file;
};

struct dijkstraEntry
{
    int shortest_distance;
    int previous_node;
    bool visited;
};

// Subject to change depending on network demands
float getBaudRate()
{
    return 10.7f;
}
// Subject to change depending on network demands
int getModulation(int distance)
{
    if(distance > 0 && distance <= 800) return 4;       // 16QAM
    if(distance > 800 && distance <= 1700) return 3;    // 8QAM
    if(distance > 1700 && distance <= 4600) return 2;   // QPSK
    if(distance > 4600 && distance <= 9300) return 1;   // BPSK
    return -1;
}

class Graph
{

    public:
    Graph(const int new_id, int t_sort, int t_algorithm)
    {
        id = new_id;
        sort_order = static_cast<e_sort_order>(t_sort);
        policy = static_cast<policy_type>(t_algorithm);

        // If input values from file are incorrect
        if(sort_order < e_sort_order::none || sort_order >= e_sort_order::max_sort)
            std::cout << "Warning! Invalid sort order, no sorting selected by default\n";
        if(policy < policy_type::none_selected || policy >= policy_type::max_pol)
            std::cout << "Warning! Invalid policy type, no spread spectrum policy selected by default\n";
        
        for(int i = 0; i < MAX_NODE; ++i)
        {
            for(int j = 0; j < MAX_NODE; ++j)
            {
                adjacency_m[i][j] = -1;
                connection_m[i][j] = -1;

                links[i][j] = new link();
            }
            dijkstra_table[i].previous_node = 0;
            dijkstra_table[i].shortest_distance = 0;
            dijkstra_table[i].visited = false;
        }
    }
    ~Graph()
    {
        for(int i = 0; i < MAX_NODE; ++i)
            for(int j = 0; j < MAX_NODE; ++j)
                free(links[i][j]);
    }
    
    // Functions
    int yenKSP(int source, const int dest, std::vector<int> k_paths[], int k_distance[])
    {
        int valid_paths = 0;
        std::vector<std::vector<int>> B_paths;
        std::vector<int> B_distance;

        std::vector<int> path;
        int dij_total_weight;
        shortest_path_dij(source, dest, path, dij_total_weight);      // Fill K_paths[0]
        k_paths[0] = path;
        k_distance[0] = dij_total_weight;

        for(int k_index = 1; k_index < K_LIMIT; ++k_index)
        {
            for(int i = 0; i < (k_paths[k_index-1].size()-1); ++i)
            {
                int spur_node = k_paths[k_index-1][i];
                std::vector<int> root_path;
                for(int n = 0; n <= i; ++n)
                    root_path.push_back(k_paths[k_index-1][n]);

                // Hold the weight of the rootpath to be added later to total weight
                int t_weight = get_path_weight(root_path);

                for(int p = 0; p < k_index; ++p)
                {
                    bool same_paths = false;
                    for(int x = 0; x < root_path.size(); x++)
                    {
                        if(k_paths[p][x] == root_path[x])
                            same_paths = true;
                        else
                        {
                            same_paths = false;
                            break;
                        }
                    }

                    if(same_paths)
                    {
                        disconnect_link(k_paths[p][i], k_paths[p][i+1]);
                    }
                }

                // for each node rootPathNode in rootPath except spurNode:
                // remove rootPathNode from Graph;
                for(auto& node : root_path)
                {
                    if(node == spur_node) continue;

                    for(int n = 0; n < MAX_NODE; ++n)
                    {
                        disconnect_link(node, n);
                    }

                }

                if(!shortest_path_dij(spur_node+1, dest, path, dij_total_weight))
                {
                    generate_adj_m();
                    break;
                }

                dij_total_weight += t_weight;

                path.erase(path.begin());

                // Entire path is made up of the root path and spur path.
                for(int p = 0; p < path.size(); ++p)
                {
                    root_path.push_back(path[p]);
                }


                // Add the potential k-shortest path to the heap.
                bool match = false;
                for (auto& path : B_paths)
                {
                    if(check_matching_paths(path, root_path)) match = true;
                }
                if(!match)
                {
                    B_paths.push_back(root_path);
                    B_distance.push_back(dij_total_weight);
                }

                // Restore Adjacency Matrix.
                // restore nodes in rootPath to Graph;
                generate_adj_m();
            }

            if(B_paths.empty()) break;

            int min = INF, i_min = -1;
            for(int i = 0; i < B_distance.size(); ++i)
            {
                if(B_distance[i] < min)
                {
                    min = B_distance[i];
                    i_min = i;
                }
            }

            k_paths[k_index] = B_paths[i_min];
            k_distance[k_index] = B_distance[i_min];
            valid_paths++;
            B_paths.erase(B_paths.begin()+i_min);
            B_distance.erase(B_distance.begin()+i_min);
        }
        return valid_paths;
    }

    int get_path_weight(const std::vector<int>& path) const
    {
        int weight = 0;
        for(int i = 0; i < path.size()-1; ++i)
        {
            weight += adjacency_m[path[i]][path[i+1]];
        }
        return weight;
    }

    bool check_matching_paths(const std::vector<int>& path_a, const std::vector<int>& path_b)
    {
        if(path_a.size() != path_b.size()) return false;

        for (int i = 0; i < path_a.size(); ++i)
        {
            if(path_a[i] == path_b[i]) continue;

            return false;
        }
        return true;
    }

    void disconnect_link(int source, const int dest)
    {
        adjacency_m[source][dest] = -1;
        adjacency_m[dest][source] = -1;
    }

    bool shortest_path_dij(int source, int dest, std::vector<int>& path, int& total_weight)
     {
        // Shift source and Dest by -1 to be able to access their address in the array
        --source;
        --dest;
        path.clear();

        reset_dijkstra_table(source);

        int minw_index = source;

        while (true)
        {
            float total_distance = dijkstra_table[minw_index].shortest_distance;

            // Update Weights
            for(int i = 0; i < MAX_NODE; ++i)
            {
                if(i == minw_index || adjacency_m[minw_index][i] == -1 || dijkstra_table[i].visited) continue;

                if(adjacency_m[minw_index][i] + total_distance < dijkstra_table[i].shortest_distance)
                {
                    dijkstra_table[i].shortest_distance = adjacency_m[minw_index][i] + total_distance;
                    dijkstra_table[i].previous_node = minw_index;
                }
            }

            dijkstra_table[minw_index].visited = true;

            // Get node with min weight
            int temp_distance = INF, temp_index = INF;

            for(int i = 0; i < MAX_NODE; ++i)
            {
                if(dijkstra_table[i].visited) continue;

                if(dijkstra_table[i].shortest_distance <= temp_distance)
                {
                    temp_distance = dijkstra_table[i].shortest_distance;
                    temp_index = i;
                }
            }

            minw_index = temp_index;

            if(check_all_visited()) break;
        }

        std::vector<int> t_path;
        int temp_index = dest;
        // buffer_size = 0;
        int i = 0;
        while(temp_index != source)
        {
            t_path.push_back(temp_index);

            // buffer[buffer_size] = temp_index;
            temp_index = dijkstra_table[temp_index].previous_node;
            // buffer_size++;

            i++;
            if(i >= MAX_NODE || temp_index == -1)   return false;
        }
        t_path.push_back(temp_index);

        // buffer[buffer_size] = temp_index;
        total_weight = dijkstra_table[dest].shortest_distance;

        // Reverse the order of the vector
        for(int i = t_path.size()-1; i >= 0; --i)
        {
            path.push_back(t_path[i]);
        }

        return true;
    }

    void reset_dijkstra_table(int source)
    {
        for(int i = 0; i < MAX_NODE; ++i){
            dijkstra_table[i].shortest_distance = INF;
            dijkstra_table[i].previous_node = -1;
            dijkstra_table[i].visited = false;
        }
        dijkstra_table[source].shortest_distance = 0;
        dijkstra_table[source].previous_node = -1;
    }

    bool check_all_visited() const
    {
        for (int i = 0; i < MAX_NODE; ++i)
        {
            if (!dijkstra_table[i].visited) return false;
        }
        return true;
    }

    void form_connections()
    {
        std::ofstream output;
        std::string filename = "Output" + std::to_string(id) + ".txt";

        output.open(filename, std::ofstream::out);
        if(!output.is_open()) std::cout << "Warning! Could not open output file\n";
        
        for(int v = 0; v < vertices_con.size(); ++v)
        {
            const vertex& curr_vertex = vertices_con[v];
            int source = curr_vertex.source-1;
            int dest = curr_vertex.dest-1;


            // Use Yen's K-Shortest Path for RSA
            std::vector<int> k_paths[K_LIMIT];                                  // Array of all paths(vectors), from shortest to least shortest
            int k_distance[K_LIMIT];                                            // Array of all distances that correspond to their paths
            int num_paths = yenKSP(curr_vertex.source, curr_vertex.dest, k_paths, k_distance);

            int min_slot, max_slot;
            bool con_success = false;

            policy_type connection_policy = policy;
            // Remove policy if current connection policy is non-confidential
            if(!curr_vertex.confidential) connection_policy = policy_type::none_selected;

            for(int k = 0; k < num_paths; ++k)
            {
                switch (connection_policy)
                {
                case policy_type::none_selected:
                    {
                        con_success = try_connect(v, k_paths[k], k_distance[k], min_slot, max_slot);
                        break;
                    }
                case policy_type::CCP:
                    {
                        con_success = try_connectCCP(v, k_paths[k], k_distance[k], min_slot, max_slot);
                        break;
                    }
                case policy_type::FCAP:
                    {
                        con_success = try_connectFCAP(v, k_paths[k], k_distance[k], min_slot, max_slot);
                        break;
                    }
                }
                if(con_success)
                {
                    std::cout << print_connection(curr_vertex.source, curr_vertex.dest, k_paths[k], k_distance[k]) << print_slots(v, min_slot, max_slot, k_paths[k]) <<'\n';
                    output << print_connection(curr_vertex.source, curr_vertex.dest, k_paths[k], k_distance[k]) << print_slots(v, min_slot, max_slot, k_paths[k]) <<'\n';
                    
                    break;
                }
            }
            if(!con_success)
            {
                std::cout << "Connection: " <<  curr_vertex.source << " -> " << curr_vertex.dest << ": Failed\n";
            }
        }
        output.close();
    }

    bool try_connect(const int& v_index, const std::vector<int>& path, const int& distance, int& min_slot, int& max_slot)
    {
        const int Total_Slots = static_cast<int>(BANDWIDTH/FSPACING);

        // Go through all links and check for Continuity, Contiguity and Non-overlapping constraints
        int v_link[Total_Slots] = {0};

        const int req_slots = static_cast<int>(std::ceil(vertices_con[v_index].cost / (getBaudRate()*getModulation(distance))));

        // Get the state of all links
        for(int link_i = 0; link_i < path.size()-1; ++link_i)
        {
            for(int slot_i = 0; slot_i < Total_Slots; ++slot_i)
            {
                if(links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[0] || v_link[slot_i])
                    v_link[slot_i] = 1;
                else
                    v_link[slot_i] = 0;
            }
        }


        // Using the current state of all relevant links, allocate continuous slots as required
        bool try_connect = true;
        for(int slot_i = 0; slot_i < Total_Slots; ++slot_i)
        {
            if(!v_link[slot_i])
            {
                for(int i = slot_i+1; i < slot_i + req_slots; ++i)
                {
                    if(v_link[i])
                    {
                        slot_i = i;
                        try_connect = false;
                        break;
                    }
                }
                // Checked if connection fits here and it does
                if(try_connect)
                {
                    min_slot = slot_i;
                    max_slot = slot_i + req_slots - 1;
                    for(int i = slot_i; i < slot_i + req_slots; ++i)
                    {
                        v_link[i] = v_index + 1;
                    }
                    break;
                }
            }
        }

        if(!try_connect)
        {
            // std::cout << "Connection: " << v_index + 1 << " could not be allocated\n";
            return false;
        }

        // Update alloc
        for(int link_i = 0; link_i < path.size()-1; ++link_i)
        {
            for(int slot_i = min_slot; slot_i <= max_slot; ++slot_i)
            {
                links[path[link_i]][path[link_i+1]]->slot[slot_i].assign_code(0, v_link[slot_i]);
                // links[path[link_i+1]][path[link_i]]->slot[slot_i].assign_code(0, v_link[slot_i]);
            }
        }
        return true;
    }

    bool try_connectCCP(const int& v_index, const std::vector<int>& path, const int& distance, int& min_slot, int& max_slot)
    {
        const int total_slots = static_cast<int>(BANDWIDTH/FSPACING);

        slot v_link[total_slots];
        slot v_slot;
        int code_index = -1;

        // Get the state of all links
        for(int link_i = 0; link_i < path.size()-1; ++link_i)
        {
            for(int slot_i = 0; slot_i < total_slots; ++slot_i)
            {
                for(int i = 0; i < MAX_SF*2 - 1; ++i)
                {
                    if(v_link[slot_i].v_tree[i] == 0 && links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i] == 0)
                        v_link[slot_i].v_tree[i] = 0;
                    else if(v_link[slot_i].v_tree[i] == 0 && links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i] != 0)
                        v_link[slot_i].v_tree[i] = links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i];
                }
            }
        }
        
        int spread_factor = MAX_SF;
        while (spread_factor > 0)
        {
            const int req_slots = static_cast<int>(std::ceil(vertices_con[v_index].cost*spread_factor / (getBaudRate()*getModulation(distance))));

            // Using the current state of all relevant links, get the the cumulative state of all v_trees using a virtual slot
            // Has Code conservation constraint
            // Use the virtual slot to find a common available slot to allocate
            bool try_connect = true;
            for(int slot_i = 0; slot_i < total_slots; ++slot_i)
            {
                v_slot = v_link[slot_i];
                
                if(v_slot.available_codes > 0)
                {
                    for(int i = slot_i+1; i < slot_i + req_slots; ++i)
                    {
                        // Perform OR for the next slots with the v_slot
                        for(int j = 0; j < MAX_SF*2-1; ++j)
                        {
                            if(v_slot.v_tree[j] == 0 && v_link[i].v_tree[j] != 0)
                            {
                                v_slot.v_tree[j] = v_link[i].v_tree[j];
                                v_slot.available_codes--;
                            }
                        }
                        if(v_slot.available_codes <= 0)
                        {
                            slot_i = i;
                            try_connect = false;
                            break;
                        }
                    }
                    // Checked if connection fits here and it does
                    if(try_connect)
                    {
                        min_slot = slot_i;
                        max_slot = slot_i + req_slots - 1;
                        code_index = find_avail_code(v_slot, spread_factor);
                        if(code_index == -1) std::cout << "Error while looking for an available code slot\n";
                        break;
                    }
                }
            }

            if(!try_connect)
            {
                spread_factor = spread_factor/2;
                continue;
            }

            // Allocate slot & code
            for(int link_i = 0; link_i < path.size()-1; ++link_i)
            {
                for(int slot_i = min_slot; slot_i <= max_slot; ++slot_i)
                {
                    links[path[link_i]][path[link_i+1]]->slot[slot_i].assign_code(code_index, v_index+1);
                    // links[path[link_i+1]][path[link_i]]->slot[slot_i].assign_code(code_index, v_index+1);
                }
            }
            return true;
        }
        std::cout << "Connection: " << v_index + 1 << " could not be allocated";
        return false;
    }

    bool try_connectFCAP(const int& v_index, const std::vector<int>& path, const int& distance, int& min_slot, int& max_slot)
    {
        const int total_slots = static_cast<int>(BANDWIDTH/FSPACING);
  
        slot v_link[total_slots];
        slot v_slot;
        
	    // Get the state of all links
	    for(int link_i = 0; link_i < path.size()-1; ++link_i)
	    {
            for(int slot_i = 0; slot_i < total_slots; ++slot_i)
		    {
		        for(int i = 0; i < MAX_SF*2 - 1; ++i)
		        {
			        if(v_link[slot_i].v_tree[i] == 0 && links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i] == 0)
				        v_link[slot_i].v_tree[i] = 0;
			        else if(v_link[slot_i].v_tree[i] == 0 && links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i] != 0)
				        v_link[slot_i].v_tree[i] = links[path[link_i]][path[link_i+1]]->slot[slot_i].v_tree[i];
		        }
		    }
	    }
        
	    // Using the current state of all relevant links, allocate continuous slots as required
	    bool try_connect = true;
        
	    std::vector<int> code_indexes;
        int code_index = -1;
	    int current_speed = 0;

        const int min_req_slots = static_cast<int>(std::ceil(vertices_con[v_index].cost / (getBaudRate()*getModulation(distance))));
        const int max_req_slots = static_cast<int>(std::ceil(vertices_con[v_index].cost*MAX_SF / (getBaudRate()*getModulation(distance))));
        
	    for(int slot_i = 0; slot_i < total_slots; ++slot_i)
	    {
	        min_slot = slot_i;
	        int spread_factor = MAX_SF;
	        bool try_slots = false;
	        // Get the range of slots that have at least one code available
	        for(int i = slot_i; i < slot_i+max_req_slots; ++i)
	        {
                while (spread_factor > 0)
                {
                    if(find_avail_code(v_link[i],spread_factor) == -1)
                    {
                        try_slots = true;
                        max_slot = i-1;
                        break;
                    }
                    spread_factor = spread_factor/2;
                }
	            if (try_slots) break;
	        }

	        // Find in the range the appropriate code indexes to allocate that satisfy the network demands
	        if(max_slot - min_slot >= min_req_slots && max_slot - min_slot <= max_req_slots)
	        {
	            for(int i = min_slot; i < max_slot; ++i)
	            {
	                
	            }
	        }
	        else
	        {
	            slot_i = max_slot+1;
	        }

	        if(try_connect) break;
	    }

        if(!try_connect)
	    {
		    return false;
	    }
  
	    // Update alloc
	    for(int link_i = 0; link_i < path.size()-1; ++link_i)
	    {
	        if(max_slot - min_slot != code_indexes.size()) std::cout << "Warning! Code indexes (size) does not match with the required slots";
	        
		    for(int slot_i = min_slot; slot_i <= max_slot; ++slot_i)
		    {
		        links[path[link_i]][path[link_i+1]]->slot[slot_i].assign_code(code_indexes[slot_i], v_index+1);
		        // links[path[link_i+1]][path[link_i]]->slot[slot_i].assign_code(code_indexes[slot_i], v_index+1);
		    }
	    }
    }

    int find_avail_code(const slot& v_slot, int spread_factor)
    {
        int level_limit = MAX_SF*2-1;
        int index = level_limit - MAX_SF;

        while (level_limit > 0)
        {
            if(spread_factor == level_limit-index)
            {
                for(int i = index; i < level_limit; ++i)
                {
                    if(v_slot.v_tree[i] == 0)
                        return i;
                }
            }
            else
            {
                level_limit = level_limit/2;
                index = index/2;
            }
        }
        return -1;
    }

    void generate_adj_m()
    {
        // Fill in the Adjacency matrix
        for(const auto& vertex : vertices_adj){
            // source and Destination must be shifted by -1. (Nodes start from 1 whereas the array starts from 0)
            adjacency_m[vertex.source-1][vertex.dest-1] = vertex.cost;
            adjacency_m[vertex.dest-1][vertex.source-1] = vertex.cost;
        }
    }

    void generate_con_m()
    {
            // Fill in the Connection Matrix and get network demands
        std::vector<vertex> sorted_connections;
        std::vector<int> sorted_distances;

        for(const auto& vertex : vertices_con){
            // source and Destination must be shifted by -1. (Nodes start from 1 whereas the array starts from 0)
            int distance;
            std::vector<int> path;
            shortest_path_dij(vertex.source, vertex.dest, path, distance);

            int req_slots = static_cast<int>(std::ceil(vertex.cost / (getBaudRate()*getModulation(distance))));

            if(sort_order != e_sort_order::none)
            {
                if(sorted_connections.empty())
                {
                    sorted_connections.push_back(vertex);
                    sorted_distances.push_back(distance);
                }
                else
                {
                    int index = -1;
                    for(int i = 0; i < sorted_connections.size(); i++)
                    {
                        if(sort_order == e_sort_order::ascending)
                        {
                            if(distance < sorted_distances[i])
                            {
                                index = i;
                                break;
                            }
                        }
                        else
                        {
                            if(distance > sorted_distances[i])
                            {
                                index = i;
                                break;
                            }
                        }
                    }
                    if(index == -1) index = sorted_connections.size();

                    sorted_connections.insert(sorted_connections.begin()+index, vertex);
                    sorted_distances.insert(sorted_distances.begin()+index, distance);
                }
            }

            connection_m[vertex.source-1][vertex.dest-1] = vertex.cost;
            connection_m[vertex.dest-1][vertex.source-1] = vertex.cost;
        }
        if(sort_order != e_sort_order::none) vertices_con = sorted_connections;
    }

    void print_adj_matrix() const
    {
        std::cout << "Adjacency Matrix:  (Showing distance between links)\n\n";
        for(int row = 0; row < MAX_NODE; ++row){
            for(int col = 0; col < MAX_NODE; ++col){
                std::cout << std::setw(5) << adjacency_m[row][col];
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    void print_con_matrix() const
    {
        std::cout << "Connection Matrix: (Showing the requested transfer speed for the connection)\n\n";
        for(int row = 0; row < MAX_NODE; ++row){
            for(int col = 0; col < MAX_NODE; ++col){
                std::cout << std::setw(5) << connection_m[row][col];
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    std::string print_connection(const int& source, const int& dest, const std::vector<int>& path, const int& distance)
    {
        std::stringstream ss;
        ss.clear();

        // Connection
        ss << "(" << source << " -> " << dest << "): ";

        // Print path
        ss << "Hops: " << path.size() << ", ";
        ss << "Path{";
        for(int i = 0; i < path.size()-1; ++i)
            ss << path[i]+1 << ", ";
        ss << 1 + path[path.size() - 1] << "}";

        // Weight
        ss << ", Weight: " << distance << ", ";
        
        return ss.str();
    }

    std::string print_slots(const int& v_index, const int& min_slot, const int& max_slot, const std::vector<int>& path) const
    {
        std::stringstream ss;
        ss.clear();
        // Slots allocated
        ss << "Slots: (" << min_slot << ", " << max_slot << ") [" << links[path[0]][path[1]]->slot[min_slot].get_index(v_index);
        for (int i = min_slot+1; i <= max_slot; ++i)
        {
            ss << ", " << links[path[0]][path[1]]->slot[i].get_index(v_index);
        }
        ss << ']';

        return ss.str();
    }

    // Variables
    link* links[MAX_NODE][MAX_NODE];
    
    int adjacency_m[MAX_NODE][MAX_NODE];
    int connection_m[MAX_NODE][MAX_NODE];

    dijkstraEntry dijkstra_table[MAX_NODE];

    int id;
    e_sort_order sort_order = e_sort_order::none;
    policy_type policy = policy_type::none_selected;

    std::vector<vertex> vertices_adj;
    std::vector<vertex> vertices_con;
};

// fills the necessary data from the given graph and connections files
bool fill_graph(Graph& network, std::string& graph, std::string& connections)
{

    std::ifstream graph_file, connection_file;

    int option = 0;
    std::string buffer;

    // Read Graph.txt
    graph_file.open(graph, std::ios::in);

    if(!graph_file.is_open()){
        std::cout << "Error: Could not open input file [" << graph << "]\n\n";
        return false;
    }

    vertex new_vertex;
    while (!graph_file.eof())
    {
        char const temp = static_cast<char>(graph_file.get());
        if(static_cast<int>(temp) < -1) continue;
        if(temp == '#') break;

        if(temp == '\n')
        {
            new_vertex.cost = std::stoi(buffer);

            network.vertices_adj.push_back(new_vertex);
            option = 0;
            buffer = "";
        }

        if(temp == ' ')
        {
            switch (option)
            {
            case 0:
                {
                    new_vertex.source = std::stoi(buffer);
                    break;
                }
            case 1:
                {
                    new_vertex.dest = std::stoi(buffer);
                    break;
                }
            default:{}
            }
            buffer = "";
            option++;
        }
        else
            buffer += temp;
    }
    graph_file.close();


    // Read Connections.txt
    connection_file.open(connections, std::ios::in);

    if(!connection_file.is_open()){
        std::cout << "Error: Could not open input file [" << connections << "]\n\n";
        return false;
    }

    while (!connection_file.eof())
    {
        char const temp = static_cast<char>(connection_file.get());
        if(static_cast<int>(temp) < -1) continue;
        if(temp == '#') break;

        if(temp == '\n')
        {
            if(std::stoi(buffer))
                new_vertex.confidential = true;
            else
                new_vertex.confidential = false;

            network.vertices_con.push_back(new_vertex);
            option = 0;
            buffer = "";
        }

        if(temp == ' ')
        {
            switch (option)
            {
            case 0:
                {
                    new_vertex.source = std::stoi(buffer);
                    break;
                }
            case 1:
                {
                    new_vertex.dest = std::stoi(buffer);
                    break;
                }
            case 2:
                {
                    new_vertex.cost = std::stoi(buffer);
                    break;
                }
            default:{}
            }
            buffer = "";
            option++;
        }
        else
            buffer += temp;
    }
    connection_file.close();

    network.generate_adj_m();

    network.generate_con_m();

    return true;
}

bool read_demands(int& argc,char** argv, std::vector<demand>& demands_info)
{
    // if(argc < 2)
    // {
    //     std::cout << "Error: Not enough input arguments\n";
    //     return false;
    // }

    std::ifstream demands_file;
    // demands_file.open(argv[1], std::ifstream::in);
    demands_file.open("Demands.txt", std::ifstream::in);
    
    if(!demands_file.is_open())
    {
        std::cout << "Error: Could not open " << argv[1] << " file with demands\n";
        return false;
    }

    int option = 0;
    std::string buffer;
    demand new_demand;
    
    while (!demands_file.eof())
    {
        char const temp = static_cast<char>(demands_file.get());
        if(static_cast<int>(temp) < -1) continue;
        if(temp == '#') break;
        
        if(temp == '\n')
        {
            new_demand.connections_file = buffer; 

            demands_info.push_back(new_demand);
            
            option = 0;
            buffer = "";
        }

        if(temp == ' ')
        {
            switch (option)
            {
            case 0:
                {
                    // Add Policy Type
                    new_demand.policy = stoi(buffer);
                    break;
                }
            case 1:
                {
                    // Add sorting algorithm
                    new_demand.sorting = stoi(buffer);
                    break;
                }
            case 2:
                {
                    // Add Graph file
                    new_demand.graph_file = buffer;
                    break;
                }
            default:{}
            }
            buffer = "";
            option++;
        }
        else
            buffer += temp;
    }
    
    demands_file.close();
    
    return true;
}

std::string generate_connections(int num_con)
{
    std::ofstream connections;
    connections.open("Connections.txt", std::ios::out);

    srand (time(nullptr));
        
    int source, dest, cost;
    bool confidential;

    for(int i = 0; i < num_con; ++i)
    {
        
        source = rand() % MAX_NODE + 1;
        dest = rand() % MAX_NODE + 1;
        while (source == dest)
        {
            dest = rand() % MAX_NODE + 1;
        }
        confidential = rand() % 1;
        
        int cost_op = rand() % 4;
        switch (cost_op)
        {
        case 0:
            {
                cost = 50;
                break;
            }
        case 1:
            {
                cost = 100;
                break;
            }
        case 2:
            {
                cost = 150;
                break;
            }
        case 3:
            {
                cost = 200;
                break;
            }
        }
        

        connections << source << ' ' << dest << ' ' << cost << ' ' << confidential << '\n';
    }

    connections << '#';
    connections.close();
    
    return "Connections.txt";
}

int main(int argc,char* argv[]){
    
    std::vector<demand> demands;
    
    // reads networks demands and fills the appropriate vectors
    read_demands(argc, argv, demands);
    
    // Files to read, had problems with inputting the files as arguments on windows
    // std::string graph = "Graph14.txt";
    // std::string connections = generate_connections(10);
    // std::string connections = "Connections.txt";
    
    for (int i = 0; i < demands.size(); ++i)
    {
        // Init Graph
        Graph network(i,demands[i].sorting, demands[i].policy);
        
        // Fill Graph with the data from the Graph and Connections files
        if(!fill_graph(network, demands[i].graph_file, demands[i].connections_file)) return -1;

        network.form_connections();
    }
    
    std::cout << "End!\n";
    return 1;
}
