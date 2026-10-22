"""Task-3 feasibility probe for a degree-4 single-vector certificate (C.5 proposal): a 16-dim isotropic
subspace meets every subspace L of V_W of dim >= 67 (16+67>82) nontrivially, so a certificate could show
"L contains no nonzero jointly isotropic vector".  Here: min over unit u in L of the isotropy loss
f(u)=||L3perp(X(u) Lam X(u)^H)||^2 for random (Haar) L of dim d.  A minimum ~0 means no certificate of that
form exists for that L (numerically).  argv: orbit d restarts steps"""
import sys, torch
sys.path.insert(0,'/workspace/pful-work/code/stochastic/cert')
from common import load
from certsearch import basis
torch.set_num_threads(4)
name=sys.argv[1]; d=int(sys.argv[2]); R=int(sys.argv[3]); steps=int(sys.argv[4])
L,Xs,Lam,r=basis(load(name),torch.device('cpu')); m=Xs.shape[0]
Xc=Xs.to(torch.complex128); Lc=L.to(torch.complex128); sl=Lam.sqrt().to(torch.complex128)
def f(u):
    u=u/u.norm(); XC=torch.einsum('a,ajk->jk',u,Xc)*sl
    return ((Lc@(XC@XC.conj().T).reshape(-1)).abs()**2).sum()
for Ls in range(3):
    g=torch.Generator().manual_seed(int(sys.argv[5])+Ls)
    B,_=torch.linalg.qr(torch.randn(m,d,dtype=torch.complex128,generator=g))
    best=1e9
    for s in range(R):
        z=torch.randn(d,dtype=torch.complex128,generator=g).requires_grad_()
        opt=torch.optim.Adam([z],lr=0.02)
        for t in range(steps):
            l=f(B@z); opt.zero_grad(); l.backward(); opt.step()
        opt=torch.optim.LBFGS([z],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-18)
        def cl():
            opt.zero_grad(); l=f(B@z); l.backward(); return l
        opt.step(cl); val=float(f(B@z).detach()); best=min(best,val); print("  restart",s,"loss",val,"norm-check",float((B@z).norm()),flush=True)
    print(name,'m',m,'d',d,'L-seed',Ls,'min isotropy loss',best,flush=True)
