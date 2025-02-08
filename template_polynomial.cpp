
const ll mod = 998244353;
vi fact;
vi invfact;


int modpow(int n, ll p){
    int res = 1;
    while (p){
        if (p & 1) { res = (ll)res * n % mod; }
        n = (ll)n * n % mod;
        p >>= 1;
    }
    return res;
}


void init_fact(int n){
    fact.resize(n + 1);
    invfact.resize(n + 1);
    fact[0] = 1; invfact[0] = 1;
    for (int i = 1; i <= n; ++i){
        fact[i] = (ll)fact[i - 1] * i % mod; 
    }
    invfact[n] = modpow(fact[n], mod - 2);
    for (int i = n - 1; i >= 1; --i) {
        invfact[i] = (ll)invfact[i + 1] * (i + 1) % mod;
    }
}


int ncr(int n, int r){
    if (r > n) { return 0; }
    int res = fact[n];
    res = (ll)res * invfact[r] % mod * invfact[n - r] % mod;
    return res;
}


ll interpolate(vector<ll>& f, ll x){
    // f are f(x) at x = 0, 1, ..., n.  return f(x)
    ll n = (ll)f.size() - 1;  // degree of f(x)
    if (x <= n) { return f[x]; }
    ll res1 = 1;
    for (int j = 0; j <= n; ++j) {
        res1 *= x - j; res1 %= mod;
    }
    ll res2 = 0;
    for (int i = 0; i <= n; ++i){
        ll res_this = f[i];
        res_this *= modinv(x - i); res_this %= mod;
        res_this *= invfact[i]; res_this %= mod;
        res_this *= invfact[n - i]; res_this %= mod;
        if ((n - i) & 1){  // (-1)^(n-i)
            res_this = mod - res_this; res_this %= mod;
        }
        res2 += res_this; res2 %= mod;
    }
    return (res1 * res2) % mod;
}



// fft
using Complex = complex<double>;
const double PI = acos(-1);
int rev[1000005];
Complex fa[1000005];
Complex fb[1000005];


void change(Complex y[], int n) {
    for (int i = 0; i < n; ++i) {
        rev[i] = rev[i >> 1] >> 1;
        if (i & 1) {
            rev[i] |= n >> 1;
        }
    }
    for (int i = 0; i < n; ++i) {
        if (i < rev[i]) {
            swap(y[i], y[rev[i]]);
        }
    }
    return;
}


void fft(Complex y[], int n, int on) {  // on==1: DFT, on==-1: IDFT
    change(y, n);
    for (int h = 2; h <= n; h <<= 1) {
        Complex wn(cos(2 * PI / h), sin(2 * PI / h));
        for (int j = 0; j < n; j += h) {
            Complex w(1, 0);
            for (int k = j; k < j + h / 2; k++) {
                Complex u = y[k];
                Complex t = w * y[k + h / 2];
                y[k] = u + t;
                y[k + h / 2] = u - t;
                w = w * wn;
            }
        }
    }
    if (on == -1) {
        reverse(y + 1, y + n);
        for (int i = 0; i < n; i++) {
            y[i].real(y[i].real() / n);
        }
    }
}


vi fft_mult(const vi& a, const vi& b){
    int n = 1;
    while (n < (int)a.size() + (int)b.size()){
        n <<= 1;
    }
    assert(n <= 1000005);
    for (int i = 0; i != n; ++i){
        fa[i] = 0;
        fb[i] = 0;
        if (i < (int)a.size()){
            fa[i] = a[i];
        }
        if (i < (int)b.size()){
            fb[i] = b[i];
        }
    }
    fft(fa, n, 1);
    fft(fb, n, 1);
    for (int i = 0; i != n; ++i){
        fa[i] *= fb[i];
    }
    fft(fa, n, -1);

    vi res(n);
    for (int i = 0; i != n; ++i){
        res[i] = round(fa[i].real());
    }
    return res;
}



// ntt, chatgpt
const int MOD = 998244353;
const int ROOT = 3; // Primitive root modulo 998244353
 
// Modular exponentiation
int mod_exp(int base, int exp, int mod) {
    int result = 1;
    while (exp > 0) {
        if (exp % 2 == 1)
            result = (1LL * result * base) % mod;
        base = (1LL * base * base) % mod;
        exp /= 2;
    }
    return result;
}
 
// Perform the NTT or its inverse
void ntt(vector<int>& poly, bool invert) {
    int n = poly.size();
    int log_n = __builtin_ctz(n); // log2(n), since n is a power of 2
 
    // Bit-reversal permutation
    vector<int> rev(n);
    for (int i = 0; i < n; ++i) {
        rev[i] = (rev[i >> 1] >> 1) | ((i & 1) << (log_n - 1));
        if (i < rev[i])
            swap(poly[i], poly[rev[i]]);
    }
 
    // NTT computation
    int root = mod_exp(ROOT, (MOD - 1) / n, MOD);
    if (invert)
        root = mod_exp(root, MOD - 2, MOD);
 
    for (int len = 2; len <= n; len *= 2) {
        int wlen = mod_exp(root, n / len, MOD);
        for (int i = 0; i < n; i += len) {
            int w = 1;
            for (int j = 0; j < len / 2; ++j) {
                int u = poly[i + j];
                int v = (1LL * poly[i + j + len / 2] * w) % MOD;
                poly[i + j] = (u + v) % MOD;
                poly[i + j + len / 2] = (u - v + MOD) % MOD;
                w = (1LL * w * wlen) % MOD;
            }
        }
    }
 
    if (invert) {
        int n_inv = mod_exp(n, MOD - 2, MOD);
        for (int& x : poly)
            x = (1LL * x * n_inv) % MOD;
    }
}
 
// Multiply two polynomials
vector<int> polynomial_multiply(const vector<int>& a, const vector<int>& b) {
    int n = 1;
    while (n < (int)a.size() + (int)b.size() - 1)
        n *= 2;
    vector<int> fa(a), fb(b);
    fa.resize(n);
    fb.resize(n);
 
    ntt(fa, false);
    ntt(fb, false);
    for (int i = 0; i < n; ++i)
        fa[i] = (1LL * fa[i] * fb[i]) % MOD;
    ntt(fa, true);
 
    // Remove trailing zeros
    while (!fa.empty() && fa.back() == 0)
        fa.pop_back();
    return fa;
}

// Example usage
int main() {
    vector<int> poly1 = {1, 2, 3}; // Example polynomial 1
    vector<int> poly2 = {4, 5, 6}; // Example polynomial 2

    vector<int> result = polynomial_multiply(poly1, poly2);

    cout << "Resultant Polynomial: ";  // 4 13 28 27 18
    for (int coeff : result) {
        cout << coeff << " ";
    }
    cout << endl;

    return 0;
}
