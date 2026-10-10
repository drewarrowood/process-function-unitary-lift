import numpy as np, json, itertools as it
from scipy.optimize import linprog
from facetlp import P, c, Y, Bs, facet, B, G
import facetlp
R = json.load(open('/workspace/stoch/reps.json'))
def Pm(w):
    M = np.zeros((8, 8))
    for o in B: M[B.index(w(o)), B.index(o)] = 1
    return M
x = (Pm(lambda o: (o[2], o[0], o[1])) + Pm(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2
for name, xx in [('eex1', x), ('orbit7', np.array(R[7][0]).reshape(8, 8)), ('orbit32', np.array(R[32][0]).reshape(8, 8))]:
    F = facet(xx); T = np.array(F['canon'])
    tight = np.nonzero(np.abs(Y @ F['f'] - 1) < 1e-7)[0]
    rk = np.linalg.matrix_rank(Y[tight[1:]] - Y[tight[0]])
    # sparse integer-ish representative: min |g|_1 s.t. g.p = h  for all PFs (h = 1 on tight ... general affine)
    vals = Y @ F['f']                       # f.(p-c) for each PF; inequality: f.(p-c) <= 1
    Pf = P.reshape(744, -1)
    A_eq = np.c_[Pf, -Pf, -np.ones(744), np.ones(744)]   # g = g+ - g-, offset t = t+ - t-
    r = linprog(np.r_[np.ones(128), 0, 0], A_eq=A_eq, b_eq=vals, bounds=[(0, None)] * 130, method='highs')
    g = (r.x[:64] - r.x[64:128]).reshape(8, 8); t = r.x[128] - r.x[129]
    sc = 1 / np.abs(g[np.abs(g) > 1e-9]).min()
    print(name, 'tight', len(tight), 'affine rank of tight set', rk, '(facet iff 36)')
    print('  inequality: sum g[i,o] p(i|o) <=', round((1 + t) * sc, 4), ' with g =')
    for i in range(8):
        print('   ', B[i], ' '.join('%5.1f' % v for v in g[i] * sc))
    print('  value at test point:', round(float((g * xx).sum() * sc), 4))
