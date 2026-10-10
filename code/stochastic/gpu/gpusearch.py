"""Batched gradient search for AFNB purifications of 3-party binary classical processes (PyTorch, CUDA or CPU).

Reduced AFNB Theorem 4 (paper Appendix C.2): find real/complex coefficient matrix C (m x r), first column c0 = coords of W,
with  L3perp(X_i Lam X_j^T) = 0  for all i,j  and  <w_i|w_j> = Tr(W) delta_ij.
Residual = sum of squared violations; ~0 => purification (verified again in float64).
"""
import argparse, itertools as it, json, os, time, numpy as np, torch

B3 = list(it.product((0, 1), repeat=3))

def _TR(X, s):
    T = X.reshape([2] * 12); tr = np.trace(T, axis1=s, axis2=s + 6)
    tr = np.expand_dims(np.expand_dims(tr, s), s + 6) / 2
    e = np.eye(2).reshape([2 if i in (s, s + 6) else 1 for i in range(12)])
    return (tr * e).reshape(64, 64)

def _Lperp3(X):
    out = np.zeros_like(X); P = [(0, 1), (2, 3), (4, 5)]
    for r in (1, 2, 3):
        for K in it.combinations(range(3), r):
            Y = X
            for j in range(3):
                if j not in K: Y = _TR(_TR(Y, P[j][0]), P[j][1])
            for k in K: Y = Y - _TR(Y, P[k][1])
            out = out + Y
    return out

_L = None
def Lmat():
    global _L
    if _L is None:
        _L = np.zeros((4096, 4096))
        for i in range(4096):
            e = np.zeros(4096); e[i] = 1; _L[:, i] = _Lperp3(e.reshape(64, 64)).ravel()
    return _L

def diagW(E):
    d = np.zeros(64)
    for xi, x in enumerate(B3):
        for ai, a in enumerate(B3):
            idx = 0
            for k in range(3): idx = idx * 4 + x[k] * 2 + a[k]
            d[idx] = E[xi, ai]
    return d

def prep(E, dev):
    """Return (T [m,m,k] compressed constraint tensor, G [m,m], c0 [m], r, m, trW) as float64 torch tensors on dev."""
    L = torch.tensor(Lmat(), dtype=torch.float64, device=dev)
    d = diagW(E); supp = np.nonzero(d > 1e-12)[0]; r = len(supp)
    emb = torch.zeros(4096, 64 * r, dtype=torch.float64, device=dev)
    for k, p in enumerate(supp):
        emb[torch.arange(64) * 64 + int(p), torch.arange(64) * r + k] = 1
    A = L @ emb
    U, s, Vh = torch.linalg.svd(A, full_matrices=True)
    rk = int((s > 1e-9 * s[0]).sum()); N = Vh[rk:].T            # null space basis (64r x m)
    m = N.shape[1]
    Xs = (emb @ N).T.reshape(m, 64, 64)
    Lam = torch.zeros(64, dtype=torch.float64, device=dev); Lam[supp] = torch.tensor(1 / d[supp], device=dev)
    XL = Xs * Lam
    # Gram of the linear map vec(c c^T) -> constraint space, compressed isometrically
    T = torch.empty(m, m, 4096, dtype=torch.float64, device=dev)
    for a in range(m):
        Y = torch.einsum('ij,bkj->bik', XL[a], Xs).reshape(m, 4096)
        T[a] = Y @ L.T
    Tm = T.reshape(m * m, 4096)
    ev, V = torch.linalg.eigh(Tm.T @ Tm)
    keep = ev > 1e-9 * ev.max(); Tc = (Tm @ V[:, keep]).reshape(m, m, int(keep.sum()))
    G = torch.einsum('aij,j,bij->ab', Xs, Lam, Xs)
    W = torch.zeros(64, 64, dtype=torch.float64, device=dev); W[supp, supp] = torch.tensor(d[supp], device=dev)
    c0 = torch.linalg.lstsq(Xs.reshape(m, -1).T, W.reshape(-1, 1)).solution[:, 0]
    assert torch.allclose(torch.einsum('a,aij->ij', c0, Xs), W, atol=1e-9)
    return Tc, G, c0, r, m, float(W.trace())

def residual(Cfree, Tc, G, c0, trW):
    """Cfree: [B, m, r-1] -> per-restart residual [B]."""
    B = Cfree.shape[0]
    C = torch.cat([c0.to(Cfree.dtype).expand(B, -1).unsqueeze(2), Cfree], 2)       # [B,m,r]
    Z = torch.einsum('abk,nbj->najk', Tc, C)                                          # [B,m,r,k]
    R = torch.einsum('nai,najk->nijk', C, Z)
    O = torch.einsum('nai,ab,nbj->nij', C, G, C) - trW * torch.eye(C.shape[2], dtype=C.dtype, device=C.device)
    return (R ** 2).sum((1, 2, 3)) + (O ** 2).sum((1, 2))

def search(E, dev, restarts=64, batch=16, iters=2000, dtype=torch.float32, seed=0, log=None, tol=1e-10):
    t0 = time.time()
    Tc64, G64, c064, r, m, trW = prep(E, dev)
    Tc, G, c0 = Tc64.to(dtype), G64.to(dtype), c064.to(dtype)
    g = torch.Generator(device='cpu').manual_seed(seed)
    scale = (trW / max(1e-12, float(G64.trace()))) ** 0.5
    best, bestC, done = float('inf'), None, 0
    while done < restarts:
        b = min(batch, restarts - done)
        X = (torch.randn(b, m, r - 1, generator=g, dtype=torch.float64) * scale).to(dev, dtype).requires_grad_()
        opt = torch.optim.LBFGS([X], lr=1, max_iter=iters, history_size=50, tolerance_grad=1e-14,
                                tolerance_change=1e-18, line_search_fn='strong_wolfe')
        def closure():
            opt.zero_grad(); f = residual(X, Tc, G, c0, trW).sum(); f.backward(); return f
        opt.step(closure)
        with torch.no_grad():
            res = residual(X, Tc, G, c0, trW)
            j = int(res.argmin())
            if float(res[j]) < best: best, bestC = float(res[j]), X[j].detach().clone()
        done += b
        if log: log(dict(restarts_done=done, best=best, secs=round(time.time() - t0, 1)))
        if best < tol * 1e3: break
    # float64 polish + verify
    X = bestC.to(torch.float64).unsqueeze(0).requires_grad_()
    opt = torch.optim.LBFGS([X], max_iter=500, tolerance_grad=1e-16, tolerance_change=1e-20, line_search_fn='strong_wolfe')
    def cl():
        opt.zero_grad(); f = residual(X, Tc64, G64, c064, trW).sum(); f.backward(); return f
    opt.step(cl)
    best64 = float(residual(X, Tc64, G64, c064, trW))
    return dict(rank=r, dimVW=m, best_residual_f32=best, best_residual_f64=best64, restarts=done,
                secs=round(time.time() - t0, 1)), X.detach()[0]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('orbits', nargs='*', type=int, help='orbit ids in reps.json')
    ap.add_argument('--named', choices=['lugano', 'eex1'])
    ap.add_argument('--reps', default=os.path.join(os.path.dirname(__file__), 'reps.json'))
    ap.add_argument('--out', default='results')
    ap.add_argument('--restarts', type=int, default=64); ap.add_argument('--batch', type=int, default=16)
    ap.add_argument('--iters', type=int, default=2000); ap.add_argument('--f64', action='store_true')
    ap.add_argument('--device', default='cuda' if torch.cuda.is_available() else 'cpu')
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True); dev = torch.device(a.device)
    R = json.load(open(a.reps)); jobs = []
    def P(w):
        M = np.zeros((8, 8))
        for o in B3: M[B3.index(w(o)), B3.index(o)] = 1
        return M
    if a.named == 'lugano': jobs.append(('lugano', P(lambda o: ((1 - o[1]) & o[2], (1 - o[2]) & o[0], (1 - o[0]) & o[1]))))
    if a.named == 'eex1': jobs.append(('eex1', (P(lambda o: (o[2], o[0], o[1])) + P(lambda o: (1 - o[2], 1 - o[0], 1 - o[1]))) / 2))
    jobs += [(f'orbit{i}', np.array(R[i][0]).reshape(8, 8)) for i in a.orbits]
    for name, E in jobs:
        ck = os.path.join(a.out, f'{name}.json')
        if os.path.exists(ck) and json.load(open(ck)).get('status') == 'done':
            print(name, 'already done'); continue
        def log(d): json.dump(dict(name=name, status='running', **d), open(ck, 'w')); print(name, d, flush=True)
        res, X = search(E, dev, a.restarts, a.batch, a.iters, torch.float64 if a.f64 else torch.float32, log=log)
        res.update(name=name, status='done', device=str(dev), found=res['best_residual_f64'] < 1e-10)
        json.dump(res, open(ck, 'w'), indent=1); print(name, res, flush=True)
        if res['found']:
            np.save(os.path.join(a.out, f'{name}_purification_coeffs.npy'), X.cpu().numpy())

if __name__ == '__main__':
    main()
