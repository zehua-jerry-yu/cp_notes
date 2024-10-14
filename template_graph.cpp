void find_maxd_c(int r, int p, vi& maxd_c, vector<vi>& adj){
    // fill maxd_c, max distance from each node to any of its children
    for (int c: adj[r]){
        if (c == p) { continue; }
        find_maxd_c(c, r, maxd_c, adj);
        maxd_c[r] = max(maxd_c[r], maxd_c[c] + 1);
    }
}


void find_maxd(int r, int p, int maxd_p, vi& maxd_c, vi& maxd, vector<vi>& adj){
    // find maxd for each node, which is max of max(maxd_c[c]) and maxd_p. O(n).
    // alternatively, see https://codeforces.com/blog/entry/114644 D for simpler sol.
    int fmaxd_c = 0;  // first max dist, i.e. max dist. should be equal to maxd_c[r].
    int smaxd_c = 0;  // second max dist
    for (int c: adj[r]){
        if (c == p) { continue; }
        if (maxd_c[c] + 1 >= fmaxd_c){
            smaxd_c = fmaxd_c; fmaxd_c = maxd_c[c] + 1;
        } else if (maxd_c[c] + 1 >= smaxd_c){
            smaxd_c = maxd_c[c] + 1;
        }
    }
    maxd[r] = max(maxd_p, fmaxd_c);
    for (int c: adj[r]){
        if (c == p) { continue; }
        find_maxd(c, r, max(maxd_p, (maxd_c[c] + 1 == fmaxd_c ? smaxd_c : fmaxd_c)) + 1, maxd_c, maxd, adj);
    }
}


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


