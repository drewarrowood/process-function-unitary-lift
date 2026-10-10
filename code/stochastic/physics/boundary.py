"""Conjecture test near the PF-hull boundary: x_t = (1-t) Lugano + t E_ex1.
t_h = largest t with x_t in conv(PF) (LP). Run the full purification search (gpusearch) at t values on both sides."""
import sys, os, json, numpy as np, itertools as it, torch
from scipy.optimize import linprog
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'gpu')); import gpusearch as gs
B = gs.B3
def Pm(w):
    M = np.zeros((8, 8))
    for o in B: M[B.index(w(o)), B.index(o)] = 1
    return M
LUG = Pm(lambda o: ((1 - o[1]) & o[2], (1 - o[2]) & o[0], (1 - o[0]) & o[1]))
EEX = (Pm(lambda o: (o[2], o[0], o[1])) + Pm(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2
PF = np.load('/workspace/stoch/pfs.npy').reshape(744, -1)
def inhull(x):
    r = linprog(np.zeros(744), A_eq=np.vstack([PF.T, np.ones(744)]), b_eq=np.r_[x.ravel(), 1], bounds=[(0, None)] * 744, method='highs')
    return r.status == 0
lo, hi = 0.0, 1.0
for _ in range(30):
    mid = (lo + hi) / 2; (lo, hi) = (mid, hi) if inhull((1 - mid) * LUG + mid * EEX) else (lo, mid)
print('t_hull =', lo, flush=True)
out = {'t_hull': lo}
for t in [float(a) for a in sys.argv[1:]]:
    res, _ = gs.search((1 - t) * LUG + t * EEX, torch.device('cpu'), restarts=8, batch=4, iters=800, dtype=torch.float64)
    out[str(t)] = res; print(t, res, flush=True)
    json.dump(out, open('/workspace/d8/boundary.json', 'w'), indent=1)
