#include <bits/stdc++.h>


using namespace std;
using ll = long long;
using vi = vector<int>;


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



void init(){
    
}



void solve(){

}


int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    init();
    int t = 1; cin >> t;
    while (t--) { solve(); }
}