vi prefix_function(string& s) {
    int n = (int)s.length();
    vi pi(n);
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        while (j > 0 && s[i] != s[j]) j = pi[j - 1];
        if (s[i] == s[j]) j++;
        pi[i] = j;
    }
    return pi;
}


vi find_occurrences(const string& text, const string& pattern) {
    string cur = pattern + '#' + text;
    int sz1 = text.size(), sz2 = pattern.size();
    vi v;
    vi lps = prefix_function(cur);
    for (int i = sz2 + 1; i <= sz1 + sz2; i++) {
        if (lps[i] == sz2){
            v.push_back(i - 2 * sz2);
        }
    }
    return v;
}


vi z_function(const string& s) {
    int n = s.size();
    vi z(n);
    int l = 0, r = 0;
    for(int i = 1; i < n; i++) {
        if(i < r) {
            z[i] = min(r - i, z[i - l]);
        }
        while(i + z[i] < n && s[z[i]] == s[i + z[i]]) {
            z[i]++;
        }
        if(i + z[i] > r) {
            l = i;
            r = i + z[i];
        }
    }
    return z;
}


vi manacher(const vi& a, bool odd) {
    int n = (int)a.size();
    vi d(n);
    if (odd) {
        // d1: odd-length palindromes. palindrome length = 2*d1[i] - 1
        int l = 0, r = -1;
        for (int i = 0; i < n; i++) {
            int k = (i > r) ? 1 : min(d[l + r - i], r - i + 1);
            while (0 <= i - k && i + k < n && a[i - k] == a[i + k]) {
                k++;
            }
            d[i] = k;
            if (i + k - 1 > r) {
                l = i - k + 1;
                r = i + k - 1;
            }
        }
    } else {
        // d2: even-length palindromes
        // d2[i] = radius of the longest evp centered between i-1 and i
        int l = 0, r = -1;
        for (int i = 0; i < n; i++) {
            int k = (i > r) ? 0 : min(d[l + r - i + 1], r - i + 1);
            while (0 <= i - k - 1 && i + k < n && a[i - k - 1] == a[i + k]) {
                k++;
            }
            d[i] = k;
            if (i + k - 1 > r) {
                l = i - k;
                r = i + k - 1;
            }
        }
    }
    return d;
}



// suffix array and lcp template.  MUST ADD $ TO S!!!!!!
// suf[0] is the pos of the smallest lexo suffix, etc.
// lcp[0] is the longest common prefix of suffix at suf[0] and suf[1]
vi suffix_array(const string& s){
    int n = s.size();
    vi a(n), c(n), h(n);
    vector<pair<char, int>> t;
    for (int i = 0; i < n; i++) t.push_back({s[i], i});
    sort(t.begin(), t.end());
    int cur = -1;
    for (int i = 0; i < n; i++){
        if (i == 0 || t[i].first != t[i - 1].first){
            cur++;
            h[cur] = i;
        }
        a[i] = t[i].second;
        c[a[i]] = cur;
    }
    vi a1(n), c1(n);
    for (int len = 1; len < n; len *= 2){
        for (int i = 0; i < n; i++){
            int j = (n + a[i] - len) % n;
            a1[h[c[j]]++] = j;
        }
        a = a1;
        cur = -1;
        for (int i = 0; i < n; i++){
            if (i == 0 || c[a[i]] != c[a[i - 1]] || c[(a[i] + len) % n] != c[(a[i - 1] + len) % n]){
                cur++;
                h[cur] = i;
            }
            c1[a[i]] = cur;
        }
        c = c1;
    }
    return a;
}
vi build_lcp(const string& s, const vi& suf){
    int n = s.size();
    vi rsuf(n), lcp(n);
    for (int i = 0; i < n; i++) rsuf[suf[i]] = i;
    int cur = 0;
    for (int i = 0; i < n; i++){
        int j = rsuf[i];
        if (j != n - 1){
            while (s[suf[j] + cur] == s[suf[j + 1] + cur]) cur++;
            lcp[j] = cur;
        }
        if (cur > 0) cur--;
    }
    return lcp;
}
