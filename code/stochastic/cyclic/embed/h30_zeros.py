"""Round 30: multistart zeros of lambda_min(M)+c on the reduced family (H.31.1); saves /tmp/r30/zeros{orb}.npy and prints angle statistics. usage: orbit NSTART seed"""
import sys, numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
for it_ in range(2500):
    opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
    if it_ in (1200,2000):
        for g_ in opt.param_groups: g_['lr']*=0.1
x=th.detach().clone().requires_grad_(True); o2=torch.optim.LBFGS([x],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-16,tolerance_change=1e-22)
def clo():
    o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
o2.step(clo); x=x.detach()
vv=lam(x,Tf,cf).numpy(); keep=vv<1e-11; print('kept',keep.sum(),'of',NS,'min',vv.min())
Z=x[keep]; np.save(f'/tmp/r30/zeros{orb}.npy',Z.numpy())
ev=torch.linalg.eigvalsh(Mmat(Z,Tf,cf)).numpy(); mult=(ev<1e-8).sum(1); print('kernel multiplicity counts',np.bincount(mult))
# Hessian rank of lambda_min (where simple)
ranks=[]
for b in range(min(len(Z),300)):
    if mult[b]!=1: continue
    H=torch.autograd.functional.hessian(lambda y: lam(y[None],Tf,cf)[0],Z[b]); e=np.linalg.eigvalsh(H.numpy()); ranks.append(int((e>1e-6).sum()))
print('Hessian rank histogram (simple kernel)',np.bincount(ranks))
w=lambda a: np.angle(np.exp(1j*a))
A=w(Z[:,:3].numpy()); Tt=w(Z[:,3:6].numpy()); P=w(Z[:,6:].numpy())
def spec(v,name):
    for k in range(3):
        near0=(np.abs(v[:,k])<1e-4).mean(); nearpi=(np.abs(np.abs(v[:,k])-np.pi)<1e-4).mean(); nearh=(np.abs(np.abs(v[:,k])-np.pi/2)<1e-4).mean()
        print(f'{name}{k}: frac ~0 {near0:.2f} ~pi {nearpi:.2f} ~pi/2 {nearh:.2f}')
spec(A,'a'); spec(Tt,'t'); spec(P,'p')
