# Minting
*Supplementary materials for **Efficient Top-k Frequent Subgraph Mining Using Tight Upper and Lower Bounds** (Submitted to VLDB 2025)*

### Dependency
- g++ compiler with c++17 support

### Usage
Compile and make an executable binary
```bash
make
```

Run Minting
```bash
./Minting -d [data graph file] -k [integer k]
```

(Example) Finding top-5 frequent subgraphs in WCGoals
```bash
./Minting -d ./dataset/WCGoals.gfu -k 5
```

Run an experiment for Minting where k is 5, 10, 15, 20, 25 on the WCGoals dataset
```bash
sh runWCGoals.sh
```

### Input File Format
[graph ID]  
[the number of vertices (n)]  
[the label of v_1]  
...  
[the label of v_n]  
[the number of edges (m)]  
[vertex ID of e_1] [vertex ID of e_1] [the label of e 1]  
...
[vertex ID of e_m] [vertex ID of e_m] [the label of e m]  

Example Input:  
#0  
3  
1  
0  
0  
2  
0 1 0  
1 2 1  
