// diameter of tree

vi maxdc(n);
vi maxdp(n);

function<void(int, int)> diamdp1 = [&](int i, int p){
    for (int c: adj[i]){
        if (c == p) { continue; }
        diamdp1(c, i);
        maxdc[i] = max(maxdc[i], maxdc[c] + 1);
    }
};

function<void(int, int)> diamdp2 = [&](int i, int p){
    int maxd1 = maxdp[i];  // largest
    int maxd2 = 0;  // second largest
    for (int c: adj[i]){
        if (c == p) { continue; }
        if (maxdc[c] + 1 >= maxd1){
            maxd2 = maxd1;
            maxd1 = maxdc[c] + 1;
        } else if (maxdc[c] + 1 >= maxd2){
            maxd2 = maxdc[c] + 1;
        }
    for (int c: adj[i]){
        if (c == p) { continue; }
        maxdp[c] = 1 + (maxdc[c] + 1 == maxd1 ? maxd2 : maxd1);
        diamdp2(c, i);
    }
};


void condense_graph(vector<vi>& adj1, vi& a1, vector<vi>& adj2, vector<ll>& a2, vi& sz){
    // condense SCC into nodes and return a DAG
    int n = adj1.size();
    int t = 0;
    vi tout(n);
    vi visited(n, 0);
    function<void(int)> dfs1 = [&](int i){
        if (visited[i]) { return; }
        visited[i] = 1;
        for (int c: adj1[i]){
            dfs1(c);
        }
        tout[i] = t;
        ++t;
    };
    for (int i = 0; i != n; ++i){
        dfs1(i);
    }
    // construct transpose graph
    vector<vi> adj_t(n);
    for (int i = 0; i != n; ++i){
        for (int c: adj1[i]){
            adj_t[c].push_back(i);
        }
    }
    // dfs on transpose graph
    vi idx(n);
    iota(idx.begin(), idx.end(), 0);
    sort(idx.begin(), idx.end(), [&](int i, int j){
        return tout[i] > tout[j];
    });

    fill(visited.begin(), visited.end(), 0);
    vi scc_id(n);
    int m = 0;  // number of SCCs
    function<void(int)> dfs2 = [&](int i){
        if (visited[i]) { return; }
        visited[i] = 1;
        scc_id[i] = m;
        for (int c: adj_t[i]){
            dfs2(c);
        }
    };
    for (int i: idx){
        if (visited[i]) { continue; }
        dfs2(i);
        ++m;
    }

    vector<set<int>> adj2_set(m);
    adj2.resize(m);
    a2.resize(m);
    sz.resize(m);
    for (int i = 0; i != n; ++i){
        a2[scc_id[i]] += a1[i];
        ++sz[scc_id[i]];
        for (int c: adj1[i]){
            if (scc_id[c] != scc_id[i]){
                adj2_set[scc_id[i]].insert(scc_id[c]);
            }
        }
    }
    for (int j = 0; j != m; ++j){
        for (int c: adj2_set[j]){
            adj2[j].push_back(c);
        }
    }
};



void find_cycle_info(  // for an undirected graph
    const vector<vector<pair<int,int>>>& adj,
    vector<bool>& node_in_cycle,
    vector<bool>& edge_in_cycle
) {
    int n = adj.size();
    int m = 0;
    for (auto& v : adj) m += v.size();
    m /= 2;

    vector<int> tin(n, -1), low(n, -1);
    vector<bool> visited(n, false);
    vector<bool> is_bridge(m, false);
    int timer = 0;

    function<void(int,int)> dfs = [&](int u, int p_edge) {
        visited[u] = true;
        tin[u] = low[u] = timer++;
        for (auto [v, id] : adj[u]) {
            if (id == p_edge) continue;
            if (visited[v]) {
                low[u] = min(low[u], tin[v]);
            } else {
                dfs(v, id);
                low[u] = min(low[u], low[v]);
                if (low[v] > tin[u]) {
                    is_bridge[id] = true;
                }
            }
        }
    };

    for (int i = 0; i < n; i++) {
        if (!visited[i]) dfs(i, -1);
    }

    vector<int> deg(n);
    for (int i = 0; i < n; i++) deg[i] = (int)adj[i].size();

    node_in_cycle.assign(n, true);
    queue<int> q;
    for (int i = 0; i < n; i++) {
        if (deg[i] <= 1) {
            q.push(i);
            node_in_cycle[i] = false;
        }
    }
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (auto [v, id] : adj[u]) {
            if (node_in_cycle[v]) {
                deg[v]--;
                if (deg[v] == 1) {
                    node_in_cycle[v] = false;
                    q.push(v);
                }
            }
        }
    }

    edge_in_cycle.assign(m, false);
    for (int i = 0; i < m; i++) {
        edge_in_cycle[i] = !is_bridge[i];
    }
}



// dfs get euler ordering. BE CAREFUL USE DP ON EULER SPACE!!!
vi euler_ordering;
vector<array<int, 2>> subtree(n);  // x,y means subtree is [x, y)
function<void(int, int)> euler = [&](int i, int p){
    subtree[i][0] = euler_ordering.size();
    euler_ordering.push_back(i);
    for (int c: adj[i]){
        if (c == p) { continue; }
        euler(c, i);
    }
    subtree[i][1] = euler_ordering.size();
};
euler(0, -1);



vi eulerian_path(int r, int m, vector<vector<pair<int, int>>> adj){
    // adj store <v, idx of edge>. 
    // return traversal of edges (can easily change to nodes).
    // r: the starting node. 
    // assume we have already check existence of eu path.
    vi res;
    vector<bool> visited(m, false);  // whether the edge is visited
    function<void(int)> dfs = [&](int i){
        while (!adj[i].empty()){
            auto [v, j] = adj[i].back();
            adj[i].pop_back();
            if (visited[j]) { continue; }
            visited[j] = true;
            dfs(v);
            res.push_back(j);
        }
    };
    dfs(r);
    return res;
};




struct LCA {
    vector<int> height, euler, first, segtree;
    vector<bool> visited;
    int n;

    LCA(vector<vector<int>> &adj, int root=0) {
        n = adj.size();
        height.resize(n);
        first.resize(n);
        euler.reserve(n * 2);
        visited.assign(n, false);
        dfs(adj, root);
        int m = euler.size();
        segtree.resize(m * 4);
        build(1, 0, m - 1);
    }

    void dfs(vector<vector<int>> &adj, int node, int h=0) {
        visited[node] = true;
        height[node] = h;
        first[node] = euler.size();
        euler.push_back(node);
        for (auto to : adj[node]) {
            if (!visited[to]) {
                dfs(adj, to, h + 1);
                euler.push_back(node);
            }
        }
    }

    void build(int node, int b, int e) {
        if (b == e) {
            segtree[node] = euler[b];
        } else {
            int mid = (b + e) / 2;
            build(node << 1, b, mid);
            build(node << 1 | 1, mid + 1, e);
            int l = segtree[node << 1], r = segtree[node << 1 | 1];
            segtree[node] = (height[l] < height[r]) ? l : r;
        }
    }

    int query(int node, int b, int e, int L, int R) {
        if (b > R || e < L)
            return -1;
        if (b >= L && e <= R)
            return segtree[node];
        int mid = (b + e) >> 1;

        int left = query(node << 1, b, mid, L, R);
        int right = query(node << 1 | 1, mid + 1, e, L, R);
        if (left == -1) return right;
        if (right == -1) return left;
        return height[left] < height[right] ? left : right;
    }

    int lca(int u, int v) {
        int left = first[u], right = first[v];
        if (left > right)
            swap(left, right);
        return query(1, 0, euler.size() - 1, left, right);
    }
};



struct FlowEdge {
    int to, cap, rev;
};
 

struct MaxFlow{
    int n;
    const int MAX = 1e8;
    vi parent;
    vector<vi> cap;  // nxn matrix
    vector<vi> adj;
 
    int bfs(int s, int t){
        parent = vi(n, -1);
        parent[s] = -2;
        queue<pair<int, int>> q;
        q.emplace(s, MAX);
        while (!q.empty()){
            auto [i, flow] = q.front();
            q.pop();
            for (int c: adj[i]){
                if (parent[c] == -1 && cap[i][c]){
                    parent[c] = i;
                    int newflow = min(flow, cap[i][c]);
                    if (c == t){
                        return newflow;
                    }
                    q.emplace(c, newflow);
                }
            }
        }
        return 0;  // did not find augmenting path
    }
 
    int maxflow(int s, int t){
        int flow = 0;
        int newflow = 0;
        while (newflow = bfs(s, t)){
            flow += newflow;
            int i = t;
            while (i != s){
                int p = parent[i];
                cap[p][i] -= newflow;
                cap[i][p] += newflow;
                i = p;
            }
        }
        return flow;
    }
 
    MaxFlow(int n_){
        n = n_;
        cap = vector<vi>(n, vi(n));
        adj = vector<vi>(n);
    }
};


struct MaxFlow{
    int n;
    const int MAX = 1e8;
    vi parent;
    vector<vi> cap;  // nxn matrix
    vector<vi> adj;
 
    int bfs(int s, int t){
        parent = vi(n, -1);
        parent[s] = -2;
        queue<pair<int, int>> q;
        q.emplace(s, MAX);
        while (!q.empty()){
            auto [i, flow] = q.front();
            q.pop();
            for (int c: adj[i]){
                if (parent[c] == -1 && cap[i][c]){
                    parent[c] = i;
                    int newflow = min(flow, cap[i][c]);
                    if (c == t){
                        return newflow;
                    }
                    q.emplace(c, newflow);
                }
            }
        }
        return 0;  // did not find augmenting path
    }
 
    int maxflow(int s, int t){
        int flow = 0;
        int newflow = 0;
        while (newflow = bfs(s, t)){
            flow += newflow;
            int i = t;
            while (i != s){
                int p = parent[i];
                cap[p][i] -= newflow;
                cap[i][p] += newflow;
                i = p;
            }
        }
        return flow;
    }
 
    MaxFlow(int n_){
        n = n_;
        cap = vector<vi>(n, vi(n));
        adj = vector<vi>(n);
    }
};


class MaxFlow {
public:
    int n, s, t, _max_flow = 0;
    vector<vector<FlowEdge>> adj;
    vi visited, parent, parent_edge;
 
    MaxFlow(int n, int s, int t) : n(n), s(s), t(t), adj(n), visited(n), parent(n), parent_edge(n) {}
 
    void add_edge(int u, int v, int cap) {
        // cout << "adding edge from " << u + 1 << " to " << v + 1 << ", cap= " << cap << "\n";
        adj[u].push_back({v, cap, (int)adj[v].size()});
        adj[v].push_back({u, 0, (int)adj[u].size() - 1});
    }
 
    bool ford_fulkerson(int ss, int tt){
        // one round of bfs with ford fulkerson
        fill(visited.begin(), visited.end(), 0);
        fill(parent.begin(), parent.end(), -1);
        queue<int> q;
        q.push(ss);
        visited[ss] = 1;
        while (!q.empty()){
            int i = q.front();
            q.pop();
            for (int j = 0; j != (int)adj[i].size(); ++j){
                const FlowEdge& e = adj[i][j];
                if (e.cap && !visited[e.to]){
                    visited[e.to] = 1;
                    parent[e.to] = i;
                    parent_edge[e.to] = j;
                    q.push(e.to);
                }
            }
        }
        return visited[tt];
    }
 
    void increment_cap(int u, int v){
        // cout << "incrementing " << u + 1 << " , " << v + 1 << "\n";
        // increment the capacity of edge from u to v
        for (FlowEdge& e: adj[u]){
            if (e.to == v){
                ++e.cap;
                return;
            }
        }
        assert(false);  // not found
    }
 
    void decrement_cap(int u, int v){
        // cout << "decrementing " << u + 1 << " , " << v + 1 << "\n";
        for (FlowEdge& e: adj[u]){
            if (e.to == v){
                if (e.cap == 0){
                    // reduce the flow of a s->u->v->t path.
                    // equivalent to reducing cap of a t->v->u->s path.
                    assert(ford_fulkerson(t, v));
                    for (int i = v; i != t; i = parent[i]){
                        int inxt = parent[i];
                        int j = parent_edge[i];
                        --adj[inxt][j].cap;
                        ++adj[i][adj[inxt][j].rev].cap;
                    }
                    assert(ford_fulkerson(u, s));
                    for (int i = s; i != u; i = parent[i]){
                        int inxt = parent[i];
                        int j = parent_edge[i];
                        --adj[inxt][j].cap;
                        ++adj[i][adj[inxt][j].rev].cap;
                    }
                    assert(adj[v][e.rev].cap > 0);
                    --adj[v][e.rev].cap;
                    ++e.cap;
                    --_max_flow;
                }
                --e.cap;
                return;
            }
        }
        assert(false);  // not found
    }
 
    int max_flow(){
        const int INF = 0x3f3f3f;
        while (ford_fulkerson(s, t)){
            int flow = INF;
            for (int v = t; v != s; v = parent[v]) {
                int u = parent[v], i = parent_edge[v];
                flow = min(flow, adj[u][i].cap);
            }
            for (int v = t; v != s; v = parent[v]) {
                int u = parent[v], i = parent_edge[v];
                adj[u][i].cap -= flow;
                adj[v][adj[u][i].rev].cap += flow;
            }
            _max_flow += flow;
        }
        return _max_flow;
    }
};
 


// MCMF template by chatgpt. O(F(VlogV+E))
// Edge structure representing flow, cost, and reverse edge index
struct Edge {
    int to, cap, cost, rev;
};

class MinCostMaxFlow {
public:
    int n;
    const int INF = 1e9;
    vector<vector<Edge>> adj; // Adjacency list
    vector<int> dist, potential, parent, parent_edge;

    // Constructor: Initializes graph with 'n' nodes
    MinCostMaxFlow(int n) : n(n), adj(n), dist(n), potential(n, 0), parent(n), parent_edge(n) {}

    // Adds an edge with capacity and cost
    void add_edge(int u, int v, int cap, int cost) {
        adj[u].push_back({v, cap, cost, (int)adj[v].size()});
        adj[v].push_back({u, 0, -cost, (int)adj[u].size() - 1});
    }

    // Dijkstra’s Algorithm to find shortest paths using reduced costs
    bool dijkstra(int s, int t) {
        fill(dist.begin(), dist.end(), INF);
        fill(parent.begin(), parent.end(), -1);
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<>> pq;

        dist[s] = 0;
        pq.push({0, s});

        while (!pq.empty()) {
            auto [d, u] = pq.top();
            pq.pop();

            if (d > dist[u]) continue; // Outdated entry, ignore

            for (int i = 0; i < (int)adj[u].size(); i++) {
                Edge &e = adj[u][i];
                if (e.cap > 0) {
                    int new_dist = dist[u] + e.cost + potential[u] - potential[e.to];
                    if (new_dist < dist[e.to]) {
                        dist[e.to] = new_dist;
                        parent[e.to] = u;
                        parent_edge[e.to] = i;
                        pq.push({new_dist, e.to});
                    }
                }
            }
        }

        // If no path to sink, return false
        if (dist[t] == INF) return false;

        // Update potentials to maintain reduced costs
        for (int i = 0; i < n; i++) {
            if (dist[i] < INF) potential[i] += dist[i];
        }
        return true;
    }

    // Computes Minimum Cost Maximum Flow
    pair<int, int> min_cost_max_flow(int s, int t) {
        int max_flow = 0, min_cost = 0;

        // Bellman-Ford to compute initial potentials
        for (int i = 0; i < n; i++) {
            for (int u = 0; u < n; u++) {
                for (Edge &e : adj[u]) {
                    if (e.cap > 0) {
                        potential[e.to] = min(potential[e.to], potential[u] + e.cost);
                    }
                }
            }
        }

        // Augment flow while there exists a valid path
        while (dijkstra(s, t)) {
            int flow = INF;

            // Find the bottleneck capacity
            for (int v = t; v != s; v = parent[v]) {
                int u = parent[v], i = parent_edge[v];
                flow = min(flow, adj[u][i].cap);
            }

            // Update residual capacities and compute total cost
            for (int v = t; v != s; v = parent[v]) {
                int u = parent[v], i = parent_edge[v];
                adj[u][i].cap -= flow;
                adj[v][adj[u][i].rev].cap += flow;
                min_cost += flow * adj[u][i].cost;
            }

            max_flow += flow;
        }
        return {max_flow, min_cost};
    }
};
