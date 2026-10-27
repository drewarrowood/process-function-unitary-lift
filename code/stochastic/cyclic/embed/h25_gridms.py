"""Round 25 (H.32.3): grid-seeded multistart over the reduced family (PF phase boards on Lugano rule 4, H.31.1; model and value
as in h24_lugsearch.py). A deterministic grid (phases 2 pi j/NA, Fibonacci Bloch directions NS per frame; NA^3*NS^3 points) is
evaluated exhaustively; from each phase triple the K lowest grid points are kept as seeds (NA^3*K seeds, deterministic), and each
seed is descended independently (batched Adam, elementwise so independent per seed; 2000 steps, lr 0.05 -> 0.005 -> 0.0005).
The best end point is polished alone with L-BFGS.  h25_grid.py (pure grid + coupled polish) failed validation on orbit 26.
usage: orbits NA NS K [chunk]   (validation: orbits 26, 30, 31 must be re-found)"""
import sys, time, itertools as it, numpy as np, torch
from h24_lugsearch import lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64); torch.set_num_threads(4)
def fib(n):
    k=np.arange(n)+0.5; th=np.arccos(1-2*k/n); ph=(np.pi*(1+5**0.5)*k)%(2*np.pi); return np.c_[th,ph]
def seeds(Tf,cf,NA,NS,K):
    A=2*np.pi*np.arange(NA)/NA; S=fib(NS)
    AA=np.array(list(it.product(A,A,A))); SS=np.array(list(it.product(range(NS),range(NS),range(NS))))
    th_t=S[SS][:,:,0]; ph_t=S[SS][:,:,1]; X=[]; vmin=np.inf
    for a in AA:
        th=np.c_[np.tile(a,(len(SS),1)),th_t,ph_t]; v=lam(torch.tensor(th),Tf,cf).numpy(); vmin=min(vmin,v.min())
        X+=list(th[np.argsort(v)[:K]])
    return np.array(X),vmin,len(AA)*len(SS)
def descend(X,Tf,cf):
    th=torch.tensor(X,requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
    for s in range(2000):
        opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
        if s in (1000,1600):
            for g_ in opt.param_groups: g_['lr']*=0.1
    return th.detach().numpy(), lam(th.detach(),Tf,cf).numpy()
def run(orb,NA,NS,K,CH,t0):
    f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
    X,gmin,ng=seeds(Tf,cf,NA,NS,K); XE=[]; VE=[]
    for c in range(0,len(X),CH):
        x,v=descend(X[c:c+CH],Tf,cf); XE.append(x); VE.append(v)
    XE=np.concatenate(XE); VE=np.concatenate(VE); j=int(np.argmin(VE))
    x=torch.tensor(XE[j:j+1],requires_grad=True)
    o2=torch.optim.LBFGS([x],max_iter=1000,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
    def clo():
        o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
    o2.step(clo); vp=float(lam(x.detach(),Tf,cf)[0])
    print(f'orbit {orb} facet {f}: grid {NA}^3 x {NS}^3 = {ng} pts (grid min {gmin:.3e}); seeds {len(X)}; descended min {VE[j]:.6e}, '
          f'polished {vp:.9e}; seeds ending below -1e-7: {(VE<-1e-7).sum()}, below -1e-9: {(VE<-1e-9).sum()}; '
          f'params {np.round(x.detach().numpy()[0],5).tolist()}  {time.time()-t0:.0f}s',flush=True)
if __name__=='__main__':
    t0=time.time(); NA,NS,K=int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]); CH=int(sys.argv[5]) if len(sys.argv)>5 else 2048
    for orb in [int(a) for a in sys.argv[1].split(',')]: run(orb,NA,NS,K,CH,t0)
