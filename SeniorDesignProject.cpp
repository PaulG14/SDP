//

#include <iostream>
#include <vector>
#include <fstream>
#include <iomanip>
#include <string>

// Graph demands
#define INF 2147483647
#define MAX_NODE 6
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
    max
};

enum algorithm_type
{
    none_selected    = 0,
    CCP     = 1,
    FCAP    = 2
};

struct slot
{
    // 0 = Code free,
    // x > 0 = x shows which connection is using the code
    // -1 = Code unavailable, child or parent has an allocated code
    int v_tree[MAX_SF*2 - 1] = {0};

    void assign_code(int index, int code)
    {
        // assign code
        v_tree[index] = code;

        disable_parent(index);
        disable_children(index);
    }
    
    int disable_children(int current_index)
    {
        int left_child = current_index*2 + 1;
        int right_child = current_index*2 + 2;

        if (left_child >= 0 && left_child < MAX_SF*2)
        {
            v_tree[left_child] = -1;
            disable_children(left_child);
        }

        if (right_child >= 0 && right_child < MAX_SF*2)
        {
            v_tree[right_child] = -1;
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

        if (parent_index >= 0 && parent_index < MAX_SF*2)
        {
            v_tree[parent_index] = -1;
            disable_parent(parent_index);
        }
    }
};

struct vertex{
    int origin;
    int dest;
    int cost;
    bool confidential = false;
};

struct dijkstraEntry{
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

class Graph{

    public:
    Graph(int t_sort, bool t_useSA, int t_algorithm)
    {
        sort_order = static_cast<e_sort_order>(t_sort);
        useSA = t_useSA;
        algorithm = static_cast<algorithm_type>(t_algorithm);
        
        if(sort_order < e_sort_order::none || sort_order >= e_sort_order::max) sort_order = e_sort_order::none;
        
        for(int i = 0; i < MAX_NODE; ++i)
        { 
            for(int j = 0; j < MAX_NODE; ++j)
            {
                adjacency_m[i][j][0].v_tree[0] = -1;
                connection_m[i][j] = -1;
                // for(int p = 1; p < static_cast<int>((BANDWIDTH/FSPACING)+1); ++p)
                // {
                //     adjacency_m[i][j][p] = 0;
                // }
            }
            dijkstra_table[i].previous_node = 0;
            dijkstra_table[i].shortest_distance = 0;
            dijkstra_table[i].visited = false;
        }
    }
    
    // Functions
    int yenKSP(int origin, int dest, std::vector<int> k_paths[], int k_distance[])
    {
        
        std::vector<std::vector<int>> B_paths;
        std::vector<int> B_distance;
        
        std::vector<int> path;
        int dij_total_weight;
        shortest_path_dij(origin, dest, path, dij_total_weight);      // Fill K_paths[0]
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
                    return k_index;
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

            B_paths.erase(B_paths.begin()+i_min);
            B_distance.erase(B_distance.begin()+i_min);
        }
        return K_LIMIT;
    }

    int get_path_weight(const std::vector<int>& path) const
    {
        int weight = 0;
        for(int i = 0; i < path.size()-1; ++i)
        {
            weight += adjacency_m[path[i]][path[i+1]][0].v_tree[0];
        }
        return weight;
    }
    
    bool check_matching_paths(std::vector<int>& path_a, std::vector<int>& path_b)
    {
        if(path_a.size() != path_b.size()) return false;
        
        for (int i = 0; i < path_a.size(); ++i)
        {
            if(path_a[i] == path_b[i]) continue;
            
            return false;
        }
        return true;
    }

    void disconnect_link(int origin, int dest)
    {
        adjacency_m[origin][dest][0].v_tree[0] = -1;
        adjacency_m[dest][origin][0].v_tree[0] = -1;
    }
    
    bool shortest_path_dij(int origin, int dest, std::vector<int>& path, int& total_weight){
        // Shift Origin and Dest by -1 to be able to access their address in the array
        --origin;
        --dest;
        path.clear();
        
        reset_dijkstratable(origin);
        
        int minw_index = origin;
        
        while (true)
        {
            float total_distance = dijkstra_table[minw_index].shortest_distance;

            // Update Weights
            for(int i = 0; i < MAX_NODE; ++i)
            {
                if(i == minw_index || adjacency_m[minw_index][i][0].v_tree[0] == -1 || dijkstra_table[i].visited) continue;

                if(adjacency_m[minw_index][i][0].v_tree[0] + total_distance < dijkstra_table[i].shortest_distance)
                {
                    dijkstra_table[i].shortest_distance = adjacency_m[minw_index][i][0].v_tree[0] + total_distance;
                    dijkstra_table[i].previous_node = minw_index;
                }
            }
            
            dijkstra_table[minw_index].visited = true;
            
            // Get node with min weight
            float temp_distance = INF;
            int temp_index = INF;
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
        while(temp_index != origin)
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
    
    void reset_dijkstratable(int origin)
    {
        for(int i = 0; i < MAX_NODE; ++i){
            dijkstra_table[i].shortest_distance = INF;
            dijkstra_table[i].previous_node = -1;
            dijkstra_table[i].visited = false;
        }
        dijkstra_table[origin].shortest_distance = 0;
        dijkstra_table[origin].previous_node = -1;
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
        for(int v = 0; v < vertices_con.size(); ++v)
        {
            const vertex& curr_vertex = vertices_con[v];
            int origin = curr_vertex.origin-1;
            int dest = curr_vertex.dest-1;
            

            // Use Yen's K-Shortest Path for RSA
            std::vector<int> k_paths[K_LIMIT];                                  // Array of all paths(vectors), from shortest to least shortest
            int k_distance[K_LIMIT];                                            // Array of all distances that correspond to their paths
            int num_paths = yenKSP(curr_vertex.origin, curr_vertex.dest, k_paths, k_distance);

            int min_slot, max_slot;
            bool con_success = false;
            for(int k = 0; k < num_paths; ++k)
            {
                if(try_connect(v, k_paths[k], k_distance[k], min_slot, max_slot))
                {
                    std::cout << "Connection: " <<  curr_vertex.origin << " -> " << curr_vertex.dest << " (" << min_slot << ", " << max_slot << ") success\n";
                    con_success = true;
                    break;
                }
            }
            if(!con_success)
                std::cout << "Connection: " <<  curr_vertex.origin << " -> " << curr_vertex.dest << " blocked\n";
        }
    }

    bool try_connect(int& v_index, std::vector<int>& path, int& distance, int& min_slot, int& max_slot)
    {
    //     const int Total_Slots = static_cast<int>(BANDWIDTH/FSPACING);
    //     const int origin = vertices_con[v_index].origin - 1;
    //     const int dest = vertices_con[v_index].dest - 1;
    //     
    //     // Go through all links and check for Continuity, Contiguity and Non-overlapping constraints
    //     int v_link[Total_Slots] = {0};
    //     
    //     int req_slots;
    //     if(useSA)
    //         req_slots = static_cast<int>((vertices_con[v_index].cost) / (getBaudRate()*getModulation(distance)));
    //     else
    //         req_slots = static_cast<int>(vertices_con[v_index].cost / (getBaudRate()*getModulation(distance)));
    //     
    //     // Get the state of all links
    //     for(int link_i = 0; link_i < path.size()-1; ++link_i)
    //     {
    //         for(int slot_i = 0; slot_i < Total_Slots; ++slot_i)
    //         {
    //             if(adjacency_m[path[link_i]][path[link_i+1]][slot_i+1] || v_link[slot_i])
    //                 v_link[slot_i] = 1;
    //             else
    //                 v_link[slot_i] = 0;
    //         }
    //     }
    //
    //     // Using the current state of all relevant links, allocate continuous slots as required
    //     bool try_connect = true;
    //     for(int slot_i = 0; slot_i < Total_Slots; ++slot_i)
    //     {
    //         if(!v_link[slot_i])
    //         {
    //             for(int i = slot_i+1; i < slot_i + req_slots; ++i)
    //             {
    //                 if(v_link[i])
    //                 {
    //                     slot_i = i;
    //                     try_connect = false;
    //                     break;
    //                 }
    //             }
    //             // Checked if connection fits here and it does
    //             if(try_connect)
    //             {
    //                 min_slot = slot_i;
    //                 max_slot = slot_i + req_slots - 1;
    //                 for(int i = slot_i; i < slot_i + req_slots; ++i)
    //                 {
    //                     v_link[i] = v_index + 1;
    //                 }
    //                 break;
    //             }
    //                 std::cout << "Connection: " << v_index + 1 << " could not be allocated";
    //         }
    //     }
    //
    //     // Update alloc
    //     if(try_connect)
    //     {
    //         for(int link_i = 0; link_i < path.size()-1; ++link_i)
    //         {
    //             for(int slot_i = 0; slot_i < Total_Slots; ++slot_i)
    //             {
    //                 adjacency_m[path[link_i]][path[link_i+1]][slot_i+1] = v_link[slot_i];
    //                 adjacency_m[path[link_i+1]][path[link_i]][slot_i+1] = v_link[slot_i];
    //             }
    //         }
    //     }
    //     
    return true;
    }
    
    void generate_adj_m()
    {
        // Fill in the Adjacency matrix
        for(const auto& vertex : vertices_adj){
            // Origin and Destination must be shifted by -1. (Nodes start from 1 whereas the array starts from 0)
            adjacency_m[vertex.origin-1][vertex.dest-1][0].v_tree[0] = vertex.cost;
            adjacency_m[vertex.dest-1][vertex.origin-1][0].v_tree[0] = vertex.cost;
        }
    }

    void generate_con_m()
    {
            // Fill in the Connection Matrix and get network demands
        std::vector<vertex> sorted_connections;
        std::vector<int> sorted_distances;
        
        for(const auto& vertex : vertices_con){
            // Origin and Destination must be shifted by -1. (Nodes start from 1 whereas the array starts from 0)
            int distance;
            std::vector<int> path;
            shortest_path_dij(vertex.origin, vertex.dest, path, distance);

            int req_slots;
            if(useSA)
                req_slots = static_cast<int>((vertex.cost) / (getBaudRate()*getModulation(distance)));
            else
                req_slots = static_cast<int>(vertex.cost / (getBaudRate()*getModulation(distance)));

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
            
            connection_m[vertex.origin-1][vertex.dest-1] = req_slots;
            connection_m[vertex.dest-1][vertex.origin-1] = req_slots;
        }
        if(sort_order != e_sort_order::none) vertices_con = sorted_connections;
    }
    
    void print_adj_matrix() const
    {
        std::cout << "Adjacency Matrix:  (Showing distance between links)\n\n";
        for(int row = 0; row < MAX_NODE; ++row){
            for(int col = 0; col < MAX_NODE; ++col){
                std::cout << std::setw(5) << adjacency_m[row][col][0].v_tree[0];
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    void print_con_matrix() const
    {
        std::cout << "Connection Matrix: (Showing the required slots for the connection)\n\n";
        for(int row = 0; row < MAX_NODE; ++row){
            for(int col = 0; col < MAX_NODE; ++col){
                std::cout << std::setw(5) << connection_m[row][col];
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    // Variables

    // All adjacency_m[i][j][0].v_tree[0] contains the distance of the 
    slot adjacency_m[MAX_NODE][MAX_NODE][static_cast<int>((BANDWIDTH/FSPACING)+1)];
    int connection_m[MAX_NODE][MAX_NODE];
    dijkstraEntry dijkstra_table[MAX_NODE];
    e_sort_order sort_order = e_sort_order::none;
    bool useSA = false;
    algorithm_type algorithm;
    
    std::vector<vertex> vertices_adj;
    std::vector<vertex> vertices_con;
};

bool read_files(Graph& network){
    
    std::ifstream graph_file, connection_file;

    int option = 0;
    std::string buffer;
    
    // Read Graph.txt
    graph_file.open("Graph.txt", std::ios::in);

    if(!graph_file.is_open()){
        // std::cout << "Error: Could not open input file [" << argv[1] << "]\n\n";
        std::cout << "Error: Could not open Graph.txt\n\n";
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
                    new_vertex.origin = std::stoi(buffer);
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
    connection_file.open("Connections.txt", std::ios::in);
    
    if(!connection_file.is_open()){
        std::cout << "Error: Could not open Connections.txt\n\n";
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
                    new_vertex.origin = std::stoi(buffer);
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

int main(int argc,char* argv[]){

    bool useSA;
    int algorithm;
    
    std::cout << "Use Spread Spectrum / Code Allocation? (Y / n, default = n): ";
    std::cin >> useSA;
    if(useSA == 'Y' || useSA == 'y')
    {
        useSA = true;
        std::cout << "Use CCP or FCAP Algorithm? (1 = CCP / 2 = FCAP, default = 2): ";
        std::cin >> algorithm;
        if(algorithm != 1)
            algorithm = 2;
    }
    else
    {
        useSA = false;
        algorithm = 0;
    }
        
    
    int sort_order;
    std::cout << "Sort connections according to weight?\n";
    std::cout << "No sort order: 0\n";
    std::cout << "Ascending Order : 1\n";
    std::cout << "Descending order : 2\n\n";
    std::cout << "Sort order : ";
    std::cin >> sort_order;
    
    Graph network(sort_order, useSA, algorithm);
    
    // Read and fill graph data in "Network" variable;
    if(!read_files(network)){
        std::cout << "Error: Failed to read file\n\n";
        return 0;
    }
    
    network.form_connections();
    
    std::cout << "End!\n";
    return 1;
}