"""Task 3 probe, radical removed. Q_t(u,v) = L3perp(X(u) Lam X(v)^H)_t. Radical R = {u : Q_t(u,.)=Q_t(.,u)=0 all t}.
For random subspaces L of dim d inside R^perp, minimise the isotropy loss over unit u in L, and report the result
next to the random-vector baseline. Loss ~0 => no 'L has no isotropic vector' certificate exists for that L.
argv: orbit d nL restarts steps"""
import sys, torch, json
sys.path.insert(0,'/workspace/pful-work/code/stochastic/cert')
from common import load
from certsearch import basis
torch.set_num_threads(int(sys.argv[6]) if len(sys.argv)>6 else 4)
name=sys.argv[1]; d=int(sys.argv[2]); nL=int(sys.argv[3]); R=int(sys.argv[4]); steps=int(sys.argv[5])
L,Xs,Lam,r=basis(load(name),torch.device('cpu')); m=Xs.shape[0]
Xc=Xs.to(torch.complex128); Lc=L.to(torch.complex128); sl=Lam.sqrt().to(torch.complex128)
XL=Xc*sl
Q=torch.stack([Lc@torch.einsum('jn,bkn->bjk',XL[a],XL.conj()).reshape(m,-1).T for a in range(m)],1)   # Q[t,a,b]
A=torch.cat([Q.permute(1,0,2).reshape(m,-1),Q.permute(2,0,1).reshape(m,-1)],1)          # u^T A = 0 (both slots)
sv=torch.linalg.svdvals(A); rad=int((sv<1e-9*sv[0]).sum())
Ufull=torch.linalg.svd(A,full_matrices=False)[0]; Rperp=Ufull[:,:m-rad]
print('m',m,'forms',Q.shape[0],'radical dim',rad,'smallest sv',[float(x) for x in sv[-3:]],flush=True)
def f(u):
    u=u/u.norm(); XC=torch.einsum('a,ajk->jk',u.conj(),XL) if False else torch.einsum('a,ajk->jk',u,XL)
    return ((Lc@(XC@XC.conj().T).reshape(-1)).abs()**2).sum()
g=torch.Generator().manual_seed(7)
base=sorted(float(f(Rperp@torch.randn(m-rad,dtype=torch.complex128,generator=g))) for _ in range(40))
print('baseline (random unit u in R^perp): min %.3g median %.3g'%(base[0],base[20]),flush=True)
for Ls in range(nL):
    B=Rperp@torch.linalg.qr(torch.randn(m-rad,d,dtype=torch.complex128,generator=g))[0]
    for s in range(R):
        z=torch.randn(d,dtype=torch.complex128,generator=g).requires_grad_()
        opt=torch.optim.Adam([z],lr=0.02)
        for t in range(steps):
            l=f(B@z); opt.zero_grad(); l.backward(); opt.step()
        opt=torch.optim.LBFGS([z],max_iter=1000,line_search_fn='strong_wolfe',tolerance_grad=1e-16,tolerance_change=1e-20)
        def cl():
            opt.zero_grad(); l=f(B@z); l.backward(); return l
        opt.step(cl)
        print(json.dumps(dict(orbit=name,d=d,L=Ls,restart=s,loss=float(f(B@z).detach()))),flush=True)
