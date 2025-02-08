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



template <typename T>
class STree{
public:
    int n = 0;
    T BASE = -1e8;                                          // CHANGE THIS
    vector<T> d;
    vector<T> laz;
    inline int lc(int j) { return 2 * j + 1; }
    inline int rc(int j) { return 2 * j + 2; }
    STree() { }
    STree(vector<T>& data){
        n = data.size();
        d.resize(4 * n, BASE);
        laz.resize(4 * n, 0);
        build(0, 0, n, data);
    }
    void push(int j, int lj, int rj){
        if (lj == rj) { return; }
        d[j] += laz[j];                                     // CHANGE THIS
        if (rj - lj > 1){
            laz[lc(j)] += laz[j];
            laz[rc(j)] += laz[j];
        }
        laz[j] = 0;
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
    void r_inc_aux(int li, int ri, T val, int j, int lj, int rj){
        push(j, lj, rj);
        if (lj >= ri || rj <= li || lj == rj) { return; }
        if (li <= lj && rj <= ri){
            laz[j] += val;
            push(j, lj, rj);
            return;
        }
        r_inc_aux(li, ri, val, lc(j), lj, (lj + rj) / 2);
        r_inc_aux(li, ri, val, rc(j), (lj + rj) / 2, rj);
        d[j] = cb(d[lc(j)], d[rc(j)]);
    }
    void r_inc(int li, int ri, T val) { r_inc_aux(li, ri, val, 0, 0, n); }
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
            laz[lc(j)] = laz[j];
            laz_set[lc(j)] = true;
            laz[rc(j)] = laz[j];
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
            laz[j] = val;
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



// template for range sum of original array, if given diff array
template <typename T>
class STree{
public:
    int n = 0;
    T BASE = 0;                                          // CHANGE THIS
    vector<T> d;   // normal sum
    vector<T> e;   // n*a[1] + (n-1)*a[2] + ... kind of sum
    vector<T> laz;
    inline int lc(int j) { return 2 * j + 1; }
    inline int rc(int j) { return 2 * j + 2; }
    STree() { }
    STree(vector<T>& data){
        n = data.size();
        d.resize(4 * n, BASE);
        e.resize(4 * n, BASE);
        laz.resize(4 * n, 0);
        build(0, 0, n, data);
    }
    void push(int j, int lj, int rj){
        if (lj == rj) { return; }
        ll p = rj - lj;
        d[j] += laz[j] * p;                                     // CHANGE THIS
        e[j] += laz[j] * (p * (p + 1) / 2);
        if (rj - lj > 1){
            laz[lc(j)] += laz[j];
            laz[rc(j)] += laz[j];
        }
        laz[j] = 0;
    }
    void build(int j, int lj, int rj, vector<T>& data){
        if (rj == lj + 1) { d[j] = data[lj]; e[j] = data[lj]; return; }
        build(lc(j), lj, (lj + rj) / 2, data);
        build(rc(j), (lj + rj) / 2, rj, data);
        d[j] = d[lc(j)] + d[rc(j)];
        e[j] = e[lc(j)] + e[rc(j)] + (rj - (lj + rj) / 2) * d[lc(j)];
    }
    void r_que_aux(int li, int ri, int j, int lj, int rj, T& resd, T& rese, int& len){
        push(j, lj, rj);
        if (lj >= ri || rj <= li || lj == rj) { resd = 0; rese = 0; len = 0; return; }
        if (lj >= li && rj <= ri) { resd = d[j]; rese = e[j]; len = rj - lj; return; }
        T resd_l = 0; T rese_l = 0; int lenl = 0;
        r_que_aux(li, ri, lc(j), lj, (lj + rj) / 2, resd_l, rese_l, lenl);
        T resd_r = 0; T rese_r = 0; int lenr = 0;
        r_que_aux(li, ri, rc(j), (lj + rj) / 2, rj, resd_r, rese_r, lenr);
        resd = resd_l + resd_r;
        rese = rese_l + rese_r + lenr * resd_l;
        len = lenl + lenr;
    }
    void r_que(int li, int ri, T& resd, T& rese){
        int len;
        return r_que_aux(li, ri, 0, 0, n, resd, rese, len);
    }
    void r_inc_aux(int li, int ri, T val, int j, int lj, int rj){
        push(j, lj, rj);
        if (lj >= ri || rj <= li || lj == rj) { return; }
        if (li <= lj && rj <= ri){
            laz[j] += val;
            push(j, lj, rj);
            return;
        }
        r_inc_aux(li, ri, val, lc(j), lj, (lj + rj) / 2);
        r_inc_aux(li, ri, val, rc(j), (lj + rj) / 2, rj);
        d[j] = d[lc(j)] + d[rc(j)];
        e[j] = e[lc(j)] + e[rc(j)] + (rj - (lj + rj) / 2) * d[lc(j)];
    }
    void r_inc(int li, int ri, T val) {
        r_inc_aux(li, ri, val, 0, 0, n);
    }
};



template <typename T>
class FTree {  // see https://oi-wiki.org/ds/fenwick/ for proof.
public:
    vector<T> d;
    FTree() { }
    FTree(int n): d(n + 1, 0) { }
    T prefix_sum(int i) {
        ++i;
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
        for (int i = 0; i != 26; ++i) { delete children[i];}
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
