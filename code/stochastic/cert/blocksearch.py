"""Matrix-valued (block) inertia certificate -- strictly generalises the single-form test.

If W (dim r) is totally isotropic for every constraint form Y(psi) (all psi in im L3perp), then for any k and any
Hermitian block matrix B = [Y(psi_pq)]_{p,q<k} (with psi_qp chosen so that B is Hermitian, psi_pq complex),
W (x) C^k is totally isotropic for B (every block vanishes on W x W). Hence
    r*k <= n0(B) + min(n+(B), n-(B)).
So lambda_{rk}(B) < 0 (or for -B) certifies non-purifiability. k=1 is the single-form test.
Usage: blocksearch.py NAME --k 2 [--steps --batch --seed --out]
"""
import argparse, json, os, time, numpy as np, torch
from common import load
from certsearch import basis

def raw(P, Xs, Lam):  # P [...,64,64] -> Y [..., m, m],  Y_ab = <P, X_a Lam X_b^T>
    sh = P.shape[:-2]; P = P.reshape(-1, 64, 64)
    A = torch.einsum('nji,ajk,k->naik', P, Xs, Lam).reshape(P.shape[0], Xs.shape[0], 4096)
    return (A @ Xs.reshape(Xs.shape[0], 4096).T).reshape(*sh, Xs.shape[0], Xs.shape[0])

def blockform(theta, L, Xs, Lam):
    """theta [B,k,k,2,4096] -> Hermitian [B, k m, k m]."""
    Bn, k = theta.shape[:2]; m = Xs.shape[0]
    Y = raw((theta @ L.T).reshape(Bn, k, k, 2, 64, 64), Xs, Lam)          # [B,k,k,2,m,m]
    Z = torch.complex(Y[:, :, :, 0], Y[:, :, :, 1])                         # block (p,q)
    Z = Z.permute(0, 1, 3, 2, 4).reshape(Bn, k * m, k * m)
    return (Z + Z.conj().transpose(1, 2)) / 2

def run(name, k, steps, batch, seed, out, dev=torch.device('cpu')):
    E = load(name); L, Xs, Lam, r = basis(E, dev); m = Xs.shape[0]; t0 = time.time()
    L32, X32, Lam32 = L.float(), Xs.float(), Lam.float(); R = r * k
    ck = os.path.join(out, f'{name}.k{k}.theta.npy')
    th = torch.randn(batch, k, k, 2, 4096, generator=torch.Generator().manual_seed(seed))
    if os.path.exists(ck): th[0] = torch.tensor(np.load(ck))
    th.requires_grad_(); opt = torch.optim.Adam([th], lr=0.05); best, bt = 1e9, None
    for it in range(steps):
        ev = torch.linalg.eigvalsh(blockform(th, L32, X32, Lam32)); n = ev.norm(dim=1)
        obj = torch.minimum(ev[:, -R], -ev[:, R - 1]) / n
        opt.zero_grad(); obj.sum().backward(); opt.step()
        j = int(obj.argmin())
        if float(obj[j]) < best: best, bt = float(obj[j]), th[j].detach().clone(); np.save(ck, bt.numpy())
        if it % 25 == 0: print(name, k, it, best, round(time.time() - t0, 1), flush=True)
        if best < -1e-3: break
    e = torch.linalg.eigvalsh(blockform(bt.double().unsqueeze(0), L, Xs, Lam)[0]); tol = 1e-9 * e.abs().max()
    npos, nneg, n0 = int((e > tol).sum()), int((e < -tol).sum()), int((e.abs() <= tol).sum())
    res = dict(name=name, k=k, m=m, r=r, obj=best, inertia=(npos, nneg, n0), bound_over_k=(n0 + min(npos, nneg)) / k,
               certified_float=bool(n0 + min(npos, nneg) < R), secs=round(time.time() - t0, 1))
    json.dump(res, open(os.path.join(out, f'{name}.k{k}.json'), 'w')); print(res, flush=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('name'); ap.add_argument('--k', type=int, default=2)
    ap.add_argument('--steps', type=int, default=300); ap.add_argument('--batch', type=int, default=2)
    ap.add_argument('--seed', type=int, default=0); ap.add_argument('--out', default='/workspace/certblock')
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True); run(a.name, a.k, a.steps, a.batch, a.seed, a.out)
