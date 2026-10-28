"""Round 30: witness search next to the zero hypersurfaces sin t_k = 0 of orbit 28: minimise lambda_min/delta^2 with t_k fixed to (0 or pi)+delta. A negative value is a crossing. usage: orbit NSTART seed"""
import sys, numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
for idx,base,name in [(3,0.,'t0=0'),(3,np.pi,'t0=pi'),(4,0.,'t1=0'),(4,np.pi,'t1=pi')]:
  for d in (1e-2,1e-3):
    th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.03)
    def full(th):
        x=th.clone(); x[:,idx]=base+d; return x
    for it_ in range(1500):
        opt.zero_grad(); v=lam(full(th),Tf,cf)/d**2; v.sum().backward(); opt.step()
        if it_==1000:
            for g_ in opt.param_groups: g_['lr']*=0.1
    v=(lam(full(th.detach()),Tf,cf)/d**2).numpy()
    print(orb,name,'delta',d,'min kappa',v.min(),'quantiles',np.quantile(v,[0.01,0.5]).round(5),flush=True)
