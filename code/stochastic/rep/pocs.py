"""Feasibility test of the Appendix E moment relaxation by cyclic projections (POCS), complex arithmetic.
Y[(i,j),(k,l)] ~ P_ik P_jl. Sets:
 A1 Hermitian and swap-symmetric Y = F Y F;
 A2 isotropy: sum_{a,c} Y[b,c,a,d] Q[a,c] = 0 for all forms Q in the span S (b,d free);
 A3 coupling: Tr_2 Y = r P, sum_j Y[i,j,j,k] = P_ik (P^2=P), tr P = r;
 K1 Y >= 0;  K2 0 <= P <= I.
(The P(x)I - Y >= 0 constraint of App. E is dropped: weaker, still sound.)
If the gap between successive projections tends to 0 the relaxation is (numerically) feasible => no certificate.
Usage: pocs.py NAME ITERS"""
import sys, os, time, json, numpy as np, torch
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'gpu'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cert'))
import gpusearch as gs
from common import load
name, iters = sys.argv[1], int(sys.argv[2]); rover = int(sys.argv[3]) if len(sys.argv) > 3 else None
Tc, G, c0, r, m, trW = gs.prep(load(name), torch.device('cpu'))
if rover: r = rover
S = Tc.numpy().reshape(m * m, -1)                     # basis of the form span, index (a,c)
Qo, _ = np.linalg.qr(S); PiS = Qo @ Qo.T              # real orthogonal projector on span
n = m * m
def A1(Y):
    Y = (Y + Y.conj().T) / 2; Y4 = Y.reshape(m, m, m, m)
    return ((Y4 + Y4.transpose(1, 0, 3, 2)) / 2).reshape(n, n)
def A2(Y):
    Y4 = Y.reshape(m, m, m, m)                        # [b,c,a,d]
    M = Y4.transpose(2, 1, 0, 3).reshape(n, n)        # [(a,c),(b,d)]
    M = M - PiS @ M
    return M.reshape(m, m, m, m).transpose(2, 1, 0, 3).reshape(n, n)
# A3: linear constraints C(P,Y) = d; build C C^* explicitly on the (m^2 + m^2 + 1)-dim constraint space
def C(P, Y):
    Y4 = Y.reshape(m, m, m, m)
    return np.concatenate([(np.einsum('ijkj->ik', Y4) - r * P).ravel(), (np.einsum('ijjk->ik', Y4) - P).ravel(), [np.trace(P) - r]])
def Cadj(z):
    z1, z2, z3 = z[:n].reshape(m, m), z[n:2 * n].reshape(m, m), z[-1]
    I = np.eye(m)
    Y = np.einsum('ik,jl->ijkl', z1, I) + np.einsum('il,jk->ijkl', z2, I).transpose(0, 1, 3, 2).transpose(0, 1, 3, 2)
    # adjoint of Y -> sum_j Y[i,j,j,k]: puts z2[i,k] at Y[i,j,j,k]
    Y = np.einsum('ik,jl->ijkl', z1, I); Y2 = np.zeros((m, m, m, m), complex)
    for j in range(m): Y2[:, j, j, :] += z2
    P = -r * z1 - z2 + z3 * I
    return P, (Y + Y2).reshape(n, n)
t0 = time.time(); N = 2 * n + 1
CC = np.zeros((N, N)); C0 = C(np.zeros((m, m), complex), np.zeros((n, n), complex)).real
for k in range(N):
    e = np.zeros(N); e[k] = 1; P_, Y_ = Cadj(e); CC[:, k] = C(P_, Y_).real - C0
CCi = np.linalg.pinv(CC); print('built C C^*', round(time.time() - t0, 1), flush=True)
def A3(P, Y):
    z = CCi @ C(P, Y).real if False else CCi.astype(complex) @ C(P, Y)
    dP, dY = Cadj(z); return P - dP, Y - dY
def K1(Y):
    w, V = np.linalg.eigh((Y + Y.conj().T) / 2); return (V * np.clip(w, 0, None)) @ V.conj().T
def K2(P):
    w, V = np.linalg.eigh((P + P.conj().T) / 2); return (V * np.clip(w, 0, 1)) @ V.conj().T
rng = np.random.default_rng(0)
P = np.eye(m) * r / m + 0j; Y = np.kron(P, P)
log = []
for it in range(iters):
    Y0, P0 = Y.copy(), P.copy()
    Y = A1(Y); Y = A2(Y); P, Y = A3(P, Y); Y = K1(Y); P = K2(P)
    # gap: violation of the affine sets at the cone point
    Y4 = Y.reshape(m, m, m, m); Mv = Y4.transpose(2, 1, 0, 3).reshape(n, n)
    gap = dict(iso=float(np.linalg.norm(PiS @ Mv)), lin=float(np.linalg.norm(C(P, Y))), sym=float(np.linalg.norm(Y - A1(Y))),
               normY=float(np.linalg.norm(Y)))
    if it % 25 == 0 or it == iters - 1:
        print(it, {k: round(v, 6) for k, v in gap.items()}, round(time.time() - t0, 1), flush=True); log.append(dict(it=it, **gap))
json.dump(dict(name=name, m=m, r=r, form_span=int(S.shape[1]), log=log), open(f'/workspace/rep/pocs_{name}_r{r}.json', 'w'))
np.save(f'/workspace/rep/PY_{name}_r{r}.npy', np.array([0], dtype=object), allow_pickle=True); np.savez(f'/workspace/rep/PY_{name}_r{r}.npz', P=P, Y=Y)
