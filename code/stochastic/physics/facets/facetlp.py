"""Facets of the PF hull (744 PFs, 3 parties binary) via polar LP: centre c = mean of PFs; in the affine span,
maximise f.(x-c) s.t. f.(p-c) <= 1 for all PFs. An optimal basic solution is a vertex of the polar = a facet.
Facet class = canonical tight-vertex set under the symmetry group (party perms x input/output relabelings, 384)."""
import numpy as np, itertools as it, json, sys
from scipy.optimize import linprog
B = list(it.product((0, 1), repeat=3))
P = np.load('/workspace/stoch/pfs.npy')                  # [744, i, o]
c = P.reshape(744, -1).mean(0)
D = P.reshape(744, -1) - c
U, s, Vt = np.linalg.svd(D, full_matrices=False); Bs = Vt[:37]   # orthonormal basis of span
Y = D @ Bs.T
key = {P[k].tobytes(): k for k in range(744)}
perms = []
for pi in it.permutations(range(3)):
    for a in it.product((0, 1), repeat=3):
        for b in it.product((0, 1), repeat=3):
            gi = [B.index(tuple(x[pi[k]] ^ a[k] for k in range(3))) for x in B]
            go = [B.index(tuple(x[pi[k]] ^ b[k] for k in range(3))) for x in B]
            perms.append((gi, go))
def act(M, g):
    gi, go = g; N = np.zeros_like(M); N[np.ix_(gi, go)] = M; return N
G = []
for g in perms:
    m = [key.get(act(P[k], g).tobytes(), -1) for k in range(744)]
    if -1 not in m: G.append(m)
print('symmetries preserving PF set:', len(G), file=sys.stderr)
def facet(x):
    y = (x.ravel() - c) @ Bs.T
    r = linprog(-y, A_ub=Y, b_ub=np.ones(744), bounds=[(None, None)] * 37, method='highs-ds')
    f = r.x; tight = tuple(np.nonzero(np.abs(Y @ f - 1) < 1e-7)[0])
    canon = min(tuple(sorted(g[t] for t in tight)) for g in G)
    return dict(viol=float(y @ f), ntight=len(tight), canon=canon, f=f)
if __name__ == '__main__':
    R = json.load(open('/workspace/stoch/reps.json'))
    def Pm(w):
        M = np.zeros((8, 8))
        for o in B: M[B.index(w(o)), B.index(o)] = 1
        return M
    tests = {'eex1': (Pm(lambda o: (o[2], o[0], o[1])) + Pm(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2}
    for k in range(len(R)): tests[f'orbit{k}'] = np.array(R[k][0]).reshape(8, 8)
    classes = {}; out = {}
    for n, x in tests.items():
        F = facet(x); cid = classes.setdefault(F['canon'], len(classes))
        out[n] = dict(class_id=cid, polar_value=round(F['viol'], 4), ntight=F['ntight'])
    json.dump(dict(tests=out, classes={str(v): list(map(int, k)) for k, v in classes.items()}), open('facet_classes.json', 'w'))
    for n, v in out.items(): print(n, v)
    print('distinct facet classes hit:', len(classes))
