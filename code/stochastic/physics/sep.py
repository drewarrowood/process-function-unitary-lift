"""Separating inequality of the PF hull for a given classical process (LP, scipy HiGHS).
max  f.x - g  s.t.  f.p <= g for all 744 PFs, -1 <= f <= 1 (64 entries of p(i|o)).  Prints violation and support."""
import numpy as np, json, sys, itertools as it
from scipy.optimize import linprog
P = np.load('pfs.npy').reshape(744, -1); B = list(it.product((0, 1), repeat=3))
def Pm(w):
    M = np.zeros((8, 8))
    for o in B: M[B.index(w(o)), B.index(o)] = 1
    return M
R = json.load(open('reps.json'))
tests = {'eex1': ((Pm(lambda o: (o[2], o[0], o[1])) + Pm(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2).ravel(),
         'orbit7': np.array(R[7][0]), 'orbit8': np.array(R[8][0]), 'mixPF': P[:5].mean(0)}
for n, x in tests.items():
    c = -np.r_[x, -1]                                  # maximise f.x - g
    A = np.c_[P, -np.ones(744)]
    r = linprog(c, A_ub=A, b_ub=np.zeros(744), bounds=[(-1, 1)] * 64 + [(None, None)], method='highs')
    f = r.x[:64]; print(n, 'violation', round(-r.fun, 4), 'nonzeros', int((np.abs(f) > 1e-9).sum()), flush=True)
