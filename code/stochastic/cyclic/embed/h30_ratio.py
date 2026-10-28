"""Round 30: minimise lambda_min/(sin^2 t0 sin^2 t1) for orbit 28 to expose zero components off the two hypersurfaces."""
import numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=28; f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
rng=np.random.default_rng(4); th=torch.tensor(rng.uniform(-np.pi,np.pi,(400,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.03)
def g(x): return lam(x,Tf,cf)/(torch.sin(x[:,3])**2*torch.sin(x[:,4])**2+1e-12)
for i in range(2000):
    opt.zero_grad(); v=g(th); v.sum().backward(); opt.step()
    if i==1400:
        for q in opt.param_groups: q['lr']*=0.1
x=th.detach(); v=g(x).numpy(); o=np.argsort(v)
np.set_printoptions(precision=3,suppress=True,linewidth=160)
print('min ratio',v[o[:10]])
w=lambda a: np.angle(np.exp(1j*a))
print(np.c_[w(x[o[:10]].numpy()), lam(x[o[:10]],Tf,cf).numpy()[:,None]])
