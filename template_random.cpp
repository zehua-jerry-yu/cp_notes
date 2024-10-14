mt19937_64 gen(chrono::steady_clock::now().time_since_epoch().count());
uniform_int_distribution<ll> rnd(0, LLONG_MAX);

shuffle(permutation.begin(), permutation.end(), gen);
ll num = rnd(gen);