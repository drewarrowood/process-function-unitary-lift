"""Degree-4 moment relaxation for 'no r-dim isotropic subspace' (sound for complex subspaces).
Variables: P (m x m Hermitian), Y (m^2 x m^2 Hermitian) standing for P (x) P.  F = swap.
Constraints (all hold for P a rank-r projector with P Q_t P = 0 for all t):
  Y >= 0,  P >= 0,  I - P >= 0,  tr P = r,  Tr_2 Y = r P,  Tr_2 (Y F) = P  (P^2 = P),  P(x)I - Y >= 0 (= P(x)(I-P)),
  isotropy: Tr_1[(Q_t (x) 1) Y F] = 0  (= P Q_t P) for the chosen forms Q_t (Hermitian parts and anti-parts).
Infeasible => certified non-purifiable.  Usage: momentsdp.py NAME K [seed]   (K random forms from the span)"""
import sys, time, numpy as np, torch, cvxpy as cp
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "cert"))
from common import load
from certsearch import basis, forms
name, K = sys.argv[1], int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
L, Xs, Lam, r = basis(load(name), torch.device('cpu')); m = Xs.shape[0]
g = torch.Generator().manual_seed(seed)
th = torch.randn(K, 2, 4096, generator=g, dtype=torch.float64)
H = forms(th, L, Xs, Lam).numpy()                      # K Hermitian m x m (random elements of the span)
H = [h / np.abs(h).max() for h in H]
n = m * m; t0 = time.time()
P = cp.Variable((m, m), hermitian=True); Y = cp.Variable((n, n), hermitian=True)
Fm = np.zeros((n, n))
for a in range(m):
    for b in range(m): Fm[a * m + b, b * m + a] = 1
YF = Y @ Fm
cons = [Y >> 0, P >> 0, np.eye(m) - P >> 0, cp.real(cp.trace(P)) == r,
        cp.partial_trace(Y, (m, m), 1) == r * P, cp.partial_trace(YF, (m, m), 1) == P,
        cp.kron(P, np.eye(m)) - Y >> 0]
for h in H:
    cons.append(cp.partial_trace(cp.kron(h, np.eye(m)) @ YF, (m, m), 0) == 0)
prob = cp.Problem(cp.Minimize(0), cons)
try:
    prob.solve(solver=cp.SCS, max_iters=3000, eps=1e-6, verbose=False)
except Exception as e:
    print('solver error', e)
print(dict(name=name, m=m, r=r, K=K, status=prob.status, secs=round(time.time() - t0, 1)), flush=True)
