"""Numerical test: does V_W contain an r-dim (complex) subspace totally isotropic for ALL forms, ignoring the
extra AFNB conditions (fixed vector c0 in the subspace, Gram normalisation)?
loss(C) = sum_{i,j} || L3perp( X(c_i) Lam X(c_j)^H ) ||^2,  C = orthonormal basis (QR) of an r-dim subspace.
If loss -> 0, no certificate based on isotropy alone (single-form, block, SDP...) can exist."""
import sys, time, torch, numpy as np
from common import load
from certsearch import basis
name = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
torch.manual_seed(seed)
L, Xs, Lam, r = basis(load(name), torch.device('cpu')); m = Xs.shape[0]
Xc = Xs.to(torch.complex128); Lc = L.to(torch.complex128)
Z = torch.randn(m, r, dtype=torch.complex128, requires_grad=True)
opt = torch.optim.Adam([Z], lr=0.02); t0 = time.time()
def loss():
    C, _ = torch.linalg.qr(Z)
    XC = torch.einsum('ai,ajk->ijk', C, Xc) * Lam.to(torch.complex128).sqrt()   # [r,64,64]: X(c_i) Lam^{1/2}
    M = torch.einsum('ijk,ljk->iljk', XC, XC.conj()).sum(-1)                      # X(c_i) Lam X(c_l)^H  [r,r,64]?
    return M
# build properly: M_il = X(c_i) Lam X(c_l)^H (64x64)
def loss2():
    C, _ = torch.linalg.qr(Z)
    XC = torch.einsum('ai,ajk->ijk', C, Xc) * Lam.to(torch.complex128).sqrt()
    M = torch.einsum('ijk,lhk->iljh', XC, XC.conj()).reshape(r * r, 4096)
    return ((M @ Lc.T).abs() ** 2).sum()
for it in range(steps):
    f = loss2(); opt.zero_grad(); f.backward(); opt.step()
    if it % 100 == 0: print(name, it, float(f), round(time.time() - t0, 1), flush=True)
print(name, 'final', float(loss2()), 'm', m, 'r', r)
