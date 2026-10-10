"""Search (torch; CUDA if available, else CPU) for a single-form non-purifiability certificate.

Purifiable => exists an r-dim subspace S of V_W on which every constraint form vanishes (paper App. C.2).
Each form Y(psi)_ab = <psi, X_a Lam X_b^T>, psi in im(L3perp), vanishes on S, hence so does its Hermitian part
H = sym(Y(psi1)) + i*anti(Y(psi2)). A totally isotropic subspace of H has dim <= n0 + min(n+, n-).
So lambda_r(H) < 0 (r-th largest eigenvalue, i.e. n+ + n0 < r) certifies NON-purifiability.
We minimise lambda_r(H)/||H|| (and the same for -H) with Adam over batched random restarts.
Note: the convex SDP relaxation {0<=P<=I, tr P=r, tr(H P)=0} is equivalent to the weaker Ky-Fan test
(sum of top-r eigenvalues < 0); it fails even on orbits 7/50, so it is reported but not relied upon.
Usage: certsearch.py NAME [--steps N --batch B --seed S --out DIR]   (NAME = orbitK | lugano | eex1)
Writes DIR/NAME.search.json (+ checkpoint DIR/NAME.theta.npy of the best theta so far; resumes).
"""
import argparse, json, os, time, numpy as np, torch
from common import gs, load

def basis(E, dev):
    L = torch.tensor(gs.Lmat(), dtype=torch.float64, device=dev)
    d = gs.diagW(E); supp = np.nonzero(d > 1e-12)[0]; r = len(supp)
    emb = torch.zeros(4096, 64 * r, dtype=torch.float64, device=dev)
    for k, p in enumerate(supp): emb[torch.arange(64) * 64 + int(p), torch.arange(64) * r + k] = 1
    _, s, Vh = torch.linalg.svd(L @ emb, full_matrices=True)
    rk = int((s > 1e-9 * s[0]).sum())
    Xs = (emb @ Vh[rk:].T).T.reshape(-1, 64, 64)
    Lam = torch.zeros(64, dtype=torch.float64, device=dev); Lam[supp] = torch.tensor(1 / d[supp], device=dev)
    return L, Xs, Lam, r

def forms(theta, L, Xs, Lam):
    """theta [B,2,4096] -> Hermitian H [B,m,m]."""
    P = (theta @ L.T).reshape(*theta.shape[:2], 64, 64)
    A = torch.einsum('nsji,ajk,k->nsaik', P, Xs, Lam).reshape(*P.shape[:2], Xs.shape[0], 4096)
    Y = A @ Xs.reshape(Xs.shape[0], 4096).T
    Hs = (Y[:, 0] + Y[:, 0].transpose(1, 2)) / 2
    Ha = (Y[:, 1] - Y[:, 1].transpose(1, 2)) / 2
    return torch.complex(Hs, Ha)          # Hs + i*Ha, Ha antisymmetric -> Hermitian

def inertia(H):
    e = torch.linalg.eigvalsh(H); tol = 1e-9 * e.abs().max()
    return int((e > tol).sum()), int((e < -tol).sum()), int((e.abs() <= tol).sum())

def search(E, dev, batch, steps, seed, ck, log):
    t0 = time.time(); L, Xs, Lam, r = basis(E, dev); m = Xs.shape[0]
    L32, X32, Lam32 = L.float(), Xs.float(), Lam.float()
    g = torch.Generator().manual_seed(seed)
    th = torch.randn(batch, 2, 4096, generator=g)
    if os.path.exists(ck): th[0] = torch.tensor(np.load(ck))          # resume from best so far
    th = th.to(dev).requires_grad_()
    opt = torch.optim.Adam([th], lr=0.05); best, bt, bkf = float('inf'), None, None
    for it in range(steps):
        ev = torch.linalg.eigvalsh(forms(th, L32, X32, Lam32)); n = ev.norm(dim=1)
        obj = torch.minimum(ev[:, -r], -ev[:, r - 1]) / n
        kf = torch.minimum(ev[:, -r:].sum(1), -ev[:, :r].sum(1)) / n
        opt.zero_grad(); obj.sum().backward(); opt.step()
        j = int(obj.argmin())
        if float(obj[j]) < best:
            best, bt, bkf = float(obj[j]), th[j].detach().clone(), float(kf[j]); np.save(ck, bt.cpu().numpy())
        if it % 25 == 0: log(dict(step=it, best=best, m=m, r=r, secs=round(time.time() - t0, 1)))
        if best < -1e-3: break
    npos, nneg, n0 = inertia(forms(bt.double().unsqueeze(0), L, Xs, Lam)[0])
    return dict(m=m, r=r, lambda_r_over_norm=best, kyfan_over_norm=bkf, inertia=(npos, nneg, n0),
                iso_bound=n0 + min(npos, nneg), certified_float=bool(n0 + min(npos, nneg) < r),
                steps=it + 1, batch=batch, seed=seed, secs=round(time.time() - t0, 1))

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('name'); ap.add_argument('--out', default='cert_results')
    ap.add_argument('--batch', type=int, default=8); ap.add_argument('--steps', type=int, default=400)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--device', default='cuda' if torch.cuda.is_available() else 'cpu')
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
    ck = os.path.join(a.out, f'{a.name}.theta.npy')
    res = search(load(a.name), torch.device(a.device), a.batch, a.steps, a.seed, ck,
                 lambda d: print(a.name, d, flush=True))
    res['name'] = a.name
    json.dump(res, open(os.path.join(a.out, f'{a.name}.search.json'), 'w'), indent=1); print(a.name, res, flush=True)
