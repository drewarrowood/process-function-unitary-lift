"""Round 32: numerical minimum of lambda_min over the region R(delta) = {|sin t0|,|sin t1| >= delta, |sin(a2/2)| >= delta}
(which excludes all five zero components of 28) and over R_c(delta) = {sum_k sin^2 t_k >= delta^2}.  Penalised Adam from random starts.  usage: orbit N seed"""
import numpy as np, torch, sys
from h24_lugsearch import Mmat
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); N=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
def lam(x): return torch.linalg.eigvalsh(Mmat(torch.cat([x,torch.zeros(x.shape[0],3)],1),Tf,cf))[:,0]
for dl in (0.3,0.1):
    x=torch.tensor(np.c_[rng.uniform(0,2*np.pi,(N,3)),rng.uniform(0,np.pi,(N,3))],requires_grad=True); opt=torch.optim.Adam([x],lr=0.01)
    def gs(x): return torch.stack([torch.sin(x[:,3])**2-dl**2,torch.sin(x[:,4])**2-dl**2,torch.sin(x[:,2]/2)**2-dl**2],1)
    for it in range(2000):
        opt.zero_grad(); v=lam(x)+10*torch.relu(-gs(x)).sum(1); v.sum().backward(); opt.step()
    ok=(gs(x)>=-1e-9).all(1); v=lam(x).detach().numpy()[ok.numpy()]
    print(f'{orb} region |sin t0|,|sin t1|,|sin(a2/2)| >= {dl}: min lambda {v.min():.4e} over {ok.sum().item()} feasible endpoints',flush=True)
