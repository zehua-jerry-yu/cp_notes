# generate a random tree
# params
n = 5
weighted = True
wmax = 100
import numpy as np

permu = np.random.permutation(n)
visited = [permu[0]]
print(n)
for i in range(1, n):
    u = permu[i]
    v = np.random.choice(visited)
    visited.append(u)
    if weighted:
        print(u+1, v+1, np.random.randint(1, wmax + 1))
    else:
        print(u+1, v+1)
