#include <bits/stdc++.h>


using namespace std;
using ll = long long;
using vi = vector<int>;


vi primes;
vector<bool> is_prime;
vi phi;
vi mu;
vi ndivs;


void init_primes(int n){
    // euler sieve
    is_prime.resize(n + 1, true);
    is_prime[0] = false;
    is_prime[1] = false;
    for (int i = 2; i <= n; ++i){
        if (is_prime[i]){
            primes.push_back(i);
        }
        for (int prime: primes){
            if (prime > n / i) { break; }
            is_prime[prime * i] = false;
            if (i % prime == 0){ break; }
        }
    }
}


void init_phi(int n){
    // euler sieve to calculate euler phi function
    assert(is_prime.size() == 0);  // make sure no repeated calculation
    is_prime.resize(n + 1, true);
    phi.resize(n + 1, 0);
    phi[1] = 1;
    for (int i = 2; i <= n; ++i){
        if (is_prime[i]){
            primes.push_back(i);
            phi[i] = i - 1;
        }
        for (int prime: primes){
            if (prime > n / i) { break; }
            is_prime[prime * i] = false;
            if (i % prime == 0){
                phi[prime * i] = phi[i] * prime;
                break;
            } else {
                phi[prime * i] = phi[i] * (prime - 1);
            }
        }
    }
}


void init_mu(int n){
    // euler sieve to calculate mobius function
    assert(is_prime.size() == 0);  // make sure no repeated calculation
    is_prime.resize(n + 1, true);
    mu.resize(n + 1, 0);
    mu[1] = 1;
    for (int i = 2; i <= n; ++i){
        if (is_prime[i]){
            primes.push_back(i);
            mu[i] = -1;
        }
        for (int prime: primes){
            if (prime > n / i) { break; }
            is_prime[prime * i] = false;
            if (i % prime == 0){
                mu[prime * i] = 0;
                break;
            } else {
                mu[prime * i] = -mu[i];
            }
        }
    }
}


void init_ndivs(int n){
    // euler sieve to calculate number of divisors
    assert(is_prime.size() == 0);  // make sure no repeated calculation
    is_prime.resize(n + 1, true);
    ndivs.resize(n + 1, 0);
    ndivs[1] = 1;
    for (int i = 2; i <= n; ++i){
        if (is_prime[i]){
            primes.push_back(i);
            ndivs[i] = 2;
        }
        for (int prime: primes){
            if (prime > n / i) { break; }
            is_prime[prime * i] = false;
            if (i % prime == 0){
                if ((i / prime) % prime == 0){
                    ndivs[prime * i] = 2 * ndivs[i] - ndivs[i / prime];
                } else {
                    ndivs[prime * i] = ndivs[i] / 2 * 3;
                }
                break;
            } else {
                ndivs[prime * i] = 2 * ndivs[i];
            }
        }
    }
}


void prime_factorization(int m, vi& m_primes, vi& m_p_ct, vi& m_factors){
    // assume primes store primes up to sqrt(m)
    for (int p: primes){
        while (m % p == 0){
            if (m_primes.empty() || m_primes.back() != p){
                m_primes.push_back(p);
                m_p_ct.push_back(0);
            }
            m /= p;
            ++m_p_ct.back();
        }
    }
    if (m > 1){
        m_primes.push_back(m);
        m_p_ct.push_back(1);
    }
    m_factors = {1};
    for (int i = 0; i != (int)m_primes.size(); ++i){
        int mult = 1;
        int sz = m_factors.size();
        for (int j = 0; j != m_p_ct[i]; ++j){
            mult *= m_primes[i];
            for (int k = 0; k != sz; ++k){
                m_factors.push_back(m_factors[k] * mult);
            }
        }
    }
}


int gcd_extended(int a, int b, int& x, int& y){
    assert(a <= b);
    if (a == 0){
        x = 0; y = 1; return b;
    }
    int x1 = 0; int y1 = 0;
    int res = gcd_extended(b % a, a, x1, y1);
    x = y1 - (b / a) * x1;
    y = x1;
    return res;
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