"""Exact verification (python-flint) of a single-form non-purifiability certificate.

theta (float, [2,4096], from certsearch.py) -> integer vector (scaled, rounded); psi_s = 64*L3perp(theta_s) exactly
(L3perp has entries in Z/64); exact integer basis X_a of V_W (nullspace over Z); with Mc = [X_1[:,c] ... X_k[:,c]]
(64 x k, c over the support of W),  Y(psi) = sum_c lam_c Mc^T psi Mc  exactly (flint matrix products);
H = sym(Y(psi_0)) + i*anti(Y(psi_1)), inertia of the real doubling [[S,-K],[K,S]] (eigenvalues doubled) from its
characteristic polynomial (real-rooted, so Descartes' rule of signs is exact).
Inertia is invariant under change of basis of V_W, so the exact basis need not match the float one.
Certified (no r-dim isotropic subspace, so NOT purifiable) iff n0 + min(n+, n-) < r.
Usage: verify.py NAME THETA.npy  -> writes NAME.verify.json and NAME.cert.npz (integer theta, exact inertia).
"""
import json, sys, time, numpy as np, flint
from fractions import Fraction
from common import gs, load

def sign_changes(cs):
    s = [c for c in cs if c != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))

def inertia_exact(M):
    p = M.charpoly(); cs = [p[i] for i in range(p.degree() + 1)]       # low -> high degree
    n0 = next(i for i, c in enumerate(cs) if c != 0)
    npos = sign_changes(cs); nneg = sign_changes([c * (-1) ** i for i, c in enumerate(cs)])
    assert npos + nneg + n0 == M.nrows()
    return npos, nneg, n0

def verify(E, theta, scale=1000):
    t0 = time.time()
    L64 = np.round(gs.Lmat() * 64).astype(np.int64); assert np.allclose(L64 / 64, gs.Lmat())
    d = gs.diagW(E); supp = [int(p) for p in np.nonzero(d > 1e-12)[0]]; r = len(supp)
    lam = [flint.fmpq(*Fraction(float(d[p])).limit_denominator(10**6).as_integer_ratio()) ** -1 for p in supp]
    emb = np.zeros((4096, 64 * r), dtype=np.int64)
    for k, p in enumerate(supp): emb[np.arange(64) * 64 + p, np.arange(64) * r + k] = 1
    A = L64 @ emb; A = A[np.abs(A).sum(1) > 0]
    N, k = flint.fmpz_mat(A.tolist()).nullspace()
    Nb = np.array(N.tolist(), dtype=object)[:, :k]              # (64r) x k, column a = X_a[:, supp] row-major
    X = Nb.reshape(64, r, k)                                      # X[i, c, a] = X_a[i, supp[c]]
    th = np.round(np.asarray(theta, float) / np.abs(theta).max() * scale).astype(np.int64)
    Ys = []
    for s in (0, 1):
        psi = flint.fmpq_mat(64, 64, [int(v) for v in L64 @ th[s]])
        Y = flint.fmpq_mat(k, k)
        for c in range(r):
            Mc = flint.fmpq_mat(64, k, [int(v) for v in X[:, c, :].ravel()])
            Y += lam[c] * (Mc.transpose() * psi * Mc)
        Ys.append(Y)
    S = (Ys[0] + Ys[0].transpose()) / 2; K = (Ys[1] - Ys[1].transpose()) / 2
    if K == flint.fmpq_mat(k, k):
        npos, nneg, n0 = inertia_exact(S); cplx = False
    else:
        D = flint.fmpq_mat(2 * k, 2 * k)
        for a in range(k):
            for b in range(k):
                D[a, b] = S[a, b]; D[a + k, b + k] = S[a, b]; D[a, b + k] = -K[a, b]; D[a + k, b] = K[a, b]
        npos, nneg, n0 = [x // 2 for x in inertia_exact(D)]; cplx = True
    bound = n0 + min(npos, nneg)
    return dict(r=r, m=k, inertia=(npos, nneg, n0), iso_bound=bound, certified=bool(bound < r), complex=cplx,
                secs=round(time.time() - t0, 1)), th

if __name__ == '__main__':
    name, tf = sys.argv[1], sys.argv[2]
    out, th = verify(load(name), np.load(tf)); out['name'] = name
    base = tf.replace('.theta.npy', '')
    np.savez(base + '.cert.npz', theta_int=th, scale=1000)
    json.dump(out, open(base + '.verify.json', 'w'), indent=1); print(out, flush=True)
