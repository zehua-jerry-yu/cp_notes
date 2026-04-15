class DSU {
public:
    vi g;
    vi sz;
    int ncc;
    DSU (int n){
        ncc = n;
        g.resize(n);
        sz.resize(n, 1);
        iota(g.begin(), g.end(), 0);
    }
    int dsu_find(int i){
        if (g[i] != i) { g[i] = dsu_find(g[i]); }
        return g[i];
    }
    void dsu_union(int i, int j){
        /* merge j into i*/
        i = dsu_find(i);
        j = dsu_find(j);
        if (i != j) {
            --ncc;
            sz[i] += sz[j];
            g[j] = i;
        }
    }
};



class DSU_2SAT {
public:
    vi g;
    int sz = 0;
    DSU_2SAT (int n) : sz(n){
        g.resize(n + 1);
        iota(g.begin(), g.end(), 0);
    }
    int dsu_find(int i){
        if (g[i] != i) {
            if (g[i] < 0){
                g[i] = -dsu_find(-g[i]);
            } else {
                g[i] = dsu_find(g[i]);
            }
        }
        return g[i];
    }
    bool dsu_try_same(int i, int j){
        int gi = dsu_find(i + 1);
        int gj = dsu_find(j + 1);
        if ((gi > 0) == (gj > 0)){
            sz -= (gi != gj);
            g[abs(gj)] = abs(gi);
        } else {
            if (-gi != gj){
                --sz;
                g[abs(gj)] = -abs(gi);
            } else {
                return false;
            }
        }
        return true;
    }
    bool dsu_try_diff(int i, int j){
        int gi = dsu_find(i + 1);
        int gj = dsu_find(j + 1);
        if ((gi > 0) == (gj > 0)){
            if (gi != gj){
                --sz;
                g[abs(gj)] = -abs(gi);
            } else {
                return false;
            }
        } else {
            sz -= (gi != -gj);
            g[abs(gj)] = abs(gi);
        }
        return true;
    }
};


struct TwoSat {
    int n;  // number of variables
    vector<vector<int>> g, rg; // implication graph and its reverse
    vector<int> order, comp;
    vector<bool> used;
    
    TwoSat(int vars) : n(vars) {
        g.resize(2 * n);
        rg.resize(2 * n);
        used.assign(2 * n, false);
        comp.assign(2 * n, -1);
        assignment.assign(n, false);
    }
    
    // x => y. for condition x OR y, call add_clause(!x, y) & add_caluse(!y, x)
    void add_clause(int x, int y) {
        // cout << "adding " << x << " " << y << "\n";
        g[x].push_back(y);
        rg[y].push_back(x);
    }
    
    // First DFS on the graph to compute the order of vertices.
    void dfs1(int v) {
        used[v] = true;
        for (int w : g[v])
            if (!used[w])
                dfs1(w);
        order.push_back(v);
    }
    
    // Second DFS on the reverse graph to assign components.
    void dfs2(int v, int cl) {
        comp[v] = cl;
        for (int w : rg[v])
            if (comp[w] == -1)
                dfs2(w, cl);
    }
    
    // Solve the 2-SAT instance.
    // Returns true if the instance is satisfiable and fills `assignment`.
    bool solve() {
        int m = 2 * n;
        for (int i = 0; i < m; i++) {
            if (!used[i])
                dfs1(i);
        }
        int cl = 0;
        for (int i = m - 1; i >= 0; i--) {
            int v = order[i];
            if (comp[v] == -1)
                dfs2(v, cl++);
        }
        // Check for each variable if it and its negation belong to the same component.
        for (int i = 0; i < n; i++) {
            if (comp[2 * i] == comp[2 * i + 1])
                return false; // unsatisfiable
        }
        return true;
    }
};


template<typename T>
struct STree {
    int n = 0;
    int N = 0;
    int H = 0;
    T BASE = -1e8;
    vector<T> t;
    vector<T> lazy;
    vector<char> lazy_set;

    STree() { }

    STree(const vector<T>& a) {
        n = (int)a.size();
        N = 1; H = 0;
        while (N < max(1, n)) { N <<= 1; ++H; }
        t.assign(2 * N, BASE);
        lazy.assign(N, BASE);
        lazy_set.assign(N, 0);
        for (int i = 0; i < n; ++i) t[N + i] = a[i];
        for (int i = N - 1; i >= 1; --i) t[i] = max(t[i<<1], t[i<<1|1]);
    }

    inline void apply_node(int p, T v) {
        t[p] = max(t[p], v);
        if (p < N) {
            if (!lazy_set[p] || lazy[p] < v) lazy[p] = v;
            lazy_set[p] = 1;
        }
    }

    inline void push(int p) {
        if (p >= N) return;
        if (!lazy_set[p]) return;
        T v = lazy[p];
        apply_node(p<<1, v);
        apply_node(p<<1|1, v);
        lazy[p] = BASE;
        lazy_set[p] = 0;
    }

    inline void pull(int p) { t[p] = max(t[p<<1], t[p<<1|1]); }

    // push all ancestors of node p (p in tree indexing)
    inline void push_path(int p) {
        for (int s = H; s > 0; --s) push(p >> s);
    }

    // range chmax [l, r)
    void r_set(int l, int r, T v) {
        if (l >= r) return;
        int L = l + N, R = r + N;
        push_path(L);
        push_path(R - 1);
        int L0 = L, R0 = R;
        while (L < R) {
            if (L & 1) apply_node(L++, v);
            if (R & 1) apply_node(--R, v);
            L >>= 1; R >>= 1;
        }
        for (int i = L0; i > 1; i >>= 1) pull(i >> 1);
        for (int i = R0 - 1; i > 1; i >>= 1) pull(i >> 1);
    }

    // range max query [l, r)
    T r_que(int l, int r) {
        if (l >= r) return BASE;
        int L = l + N, R = r + N;
        push_path(L);
        push_path(R - 1);
        T resL = BASE, resR = BASE;
        while (L < R) {
            if (L & 1) resL = max(resL, t[L++]);
            if (R & 1) resR = max(t[--R], resR);
            L >>= 1; R >>= 1;
        }
        return max(resL, resR);
    }
};


template <typename T>
class STree{
public:
    int n = 0;
    T BASE = -1e8;                                          // CHANGE THIS
    vector<T> d;
    vector<T> laz;
    vector<bool> laz_set;
    inline int lc(int j) { return 2 * j + 1; }
    inline int rc(int j) { return 2 * j + 2; }
    STree() { }
    STree(vector<T>& data){
        n = data.size();
        d.resize(4 * n, BASE);
        laz.resize(4 * n, 0);
        laz_set.resize(4 * n, false);
        build(0, 0, n, data);
    }
    void push(int j, int lj, int rj){
        if (lj == rj || !laz_set[j]) { return; }
        d[j] = laz[j];                                      // CHANGE THIS
        if (rj - lj > 1){
            laz[lc(j)] = laz[j];                                      // CHANGE THIS
            laz_set[lc(j)] = true;
            laz[rc(j)] = laz[j];                                      // CHANGE THIS
            laz_set[rc(j)] = true;
        }
        laz[j] = 0;
        laz_set[j] = false;
    }
    inline T cb(T resl, T resr){
        return max(resl, resr);                             // CHANGE THIS
    }
    void build(int j, int lj, int rj, vector<T>& data){
        if (rj == lj + 1){ d[j] = data[lj]; return; }
        build(lc(j), lj, (lj + rj) / 2, data);
        build(rc(j), (lj + rj) / 2, rj, data);
        d[j] = cb(d[lc(j)], d[rc(j)]);
    }
    T r_que_aux(int li, int ri, int j, int lj, int rj){
        push(j, lj, rj);
        if (lj >= ri || rj <= li || lj == rj) { return BASE; }
        if (lj >= li && rj <= ri) { return d[j]; }
        return cb(r_que_aux(li, ri, lc(j), lj, (lj + rj) / 2), 
            r_que_aux(li, ri, rc(j), (lj + rj) / 2, rj));
    }
    T r_que(int li, int ri) { return r_que_aux(li, ri, 0, 0, n); }
    void r_set_aux(int li, int ri, T val, int j, int lj, int rj){
        push(j, lj, rj);
        if (lj >= ri || rj <= li || lj == rj) { return; }
        if (li <= lj && rj <= ri){
            laz[j] = val;                               // CHANGE THIS
            laz_set[j] = true;
            push(j, lj, rj);
            return;
        }
        r_set_aux(li, ri, val, lc(j), lj, (lj + rj) / 2);
        r_set_aux(li, ri, val, rc(j), (lj + rj) / 2, rj);
        d[j] = cb(d[lc(j)], d[rc(j)]);
    }
    void r_set(int li, int ri, T val) { r_set_aux(li, ri, val, 0, 0, n); }
};


template <typename T>
class FTree {
public:
    vector<T> d;
    FTree() { }
    FTree(int n): d(n + 1, 0) { }
    T prefix_sum(int i) {  // sum of [0,i)
        T res = 0;
        while (i){
            res += d[i];
            i &= i - 1;
        }
        return res;
    }
    void p_inc(int i, T val) {
        ++i;
        while (i < (int)d.size()){
            d[i] += val;
            i += (i & (-i));
        }
    }
};


class Trie {
public:
    int count = 0;
    int count_subtree = 0;
    Trie* children[26] = {};
    Trie() { }
    ~Trie() {
        for (int i = 0; i != 26; ++i) { delete children[i]; }  // careful - delete does not set to nullptr!
    }
    void insert(string& word) {
        Trie* node = this;
        for (char c: word){
            ++(node -> count_subtree);
            if (!node -> children[c - 'a']) { node -> children[c - 'a'] = new Trie(); }
            node = node -> children[c - 'a'];
        }
        ++(node -> count_subtree);
        ++(node -> count);
    }
    bool search(string& word) {
        Trie* node = this;
        for (char c: word){
            if (!node -> children[c - 'a']) { return false; }
            node = node -> children[c - 'a'];
        }
        return node -> count;
    }
    bool start_with(string& prefix) {
        Trie* node = this;
        for (char c: prefix){
            if (!node -> children[c - 'a']) { return false; }
            node = node -> children[c - 'a'];
        }
        return node -> count_subtree;
    }
};
