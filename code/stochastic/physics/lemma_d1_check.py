"""Numerical sanity check of Lemma D.1 on the source-sink lift of the Lugano process function:
the sink vectors v_{o,i} = (<i| x 1_F) V |psi, o> are mutually orthogonal with norms p(i|o)."""
import numpy as np, itertools as it
B = list(it.product((0, 1), repeat=3))
w = lambda o: ((1 - o[1]) & o[2], (1 - o[2]) & o[0], (1 - o[0]) & o[1])
U = np.zeros((64, 64))
for oi, o in enumerate(B):
    for e in range(8):
        i = B.index(tuple((a + b) % 2 for a, b in zip(w(o), B[e]))); U[i * 8 + oi, oi * 8 + e] = 1
v = {(oi, i): U[:, oi * 8].reshape(8, 8)[i] for oi in range(8) for i in range(8)}
G = np.array([[v[a] @ v[b] for b in v] for a in v])
print('max off-diagonal', np.abs(G - np.diag(np.diag(G))).max(), 'trace', G.trace())
