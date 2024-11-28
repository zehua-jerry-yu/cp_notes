
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




// ntt. https://blog.csdn.net/qq_35866893/article/details/124547902
#include <bits/stdc++.h>
using namespace std;
const int MAXN=3*1e6+10;
const int mod=998244353,G=3,Gi=332748118;//绝大多数情况下如此
int n,m,limit=1,L,r[MAXN];
long long a[MAXN],b[MAXN];
long long fastpow(long long a, long long k)
{
    long long res=1ll;
    while(k)
    {
        if(k&1)
        {
            res=(res*a)%mod;
        }
        a=(a*a)%mod;
        k>>=1ll;
    }
    return res%mod;
}
void NTT(long long *A,int type)//NTT板子
{
    for(int i=0;i<limit;i++)
    {
        if(i<r[i])
        {
            swap(A[i],A[r[i]]);
        }
    }
    for(int mid=1;mid<limit;mid<<=1)
    {
        long long Wn=fastpow(type==1?G:Gi,(mod-1)/(mid<<1));
        for(int j=0;j<limit;j+=(mid<<1))
        {
            long long w = 1;
            for(int k = 0; k < mid; k++, w = (w * Wn) % mod)
            {
                 int x=A[j+k];
                 int y=w*A[j+k+mid]%mod;
                 A[j+k]=(x+y)%mod,
                 A[j+k+mid]=(x-y+mod)%mod;
            }
        }
    }
    if(type==-1)
    {
        long long inv =fastpow(limit,mod-2);
        for(int i=0;i<=n+m;i++)
        {
           A[i]=(A[i]*inv)%mod;
        }
    }
}
void poly_mul(long long *a,long long *b,int deg)//多项式乘法
{
    while(limit<=deg)
    {
        limit<<=1;
        L++;
    }
    for(int i=0;i<limit;i++)
    {
        r[i]=(r[i>>1]>>1)|((i&1)<<(L-1));
    }
    NTT(a,1);
    NTT(b,1);
    for(int i=0;i<limit;i++)
    {
        a[i]=(a[i]*b[i])%mod;
    }
    NTT(a, -1);
}
int main()
{
    cin>>n>>m;
    for(int i = 0; i <= n; i++)
    {
        cin>>a[i];
        a[i]=(a[i]+mod)%mod;
    }
    for(int i = 0; i <= m; i++)
    {
        cin>>b[i];
        b[i]=(b[i]+mod)%mod;
    }
    poly_mul(a,b,n+m);
    for(int i=0;i<=n+m;i++)
    {
        cout<<a[i]<<" ";
    }
    cout<<endl;
    return 0;
}

