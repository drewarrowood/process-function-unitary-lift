"""Round 25 (H.32.3): dense deterministic grid search over the reduced family (PF phase boards on Lugano rule 4, H.31.1; same
nine-parameter model and value as h24_lugsearch.py: value = lambda_min(M(theta)) + c, source eliminated exactly).
Grid: phases a_k in {2 pi j / NA}, Bloch directions of the three frames from a Fibonacci set of NS points (theta, phi), i.e. NA^3 * NS^3
points, evaluated exhaustively in batches; the NPOL lowest grid points (deduplicated) are then polished with L-BFGS.
usage: orbits NA NS NPOL   (validation: orbits 26, 30, 31 must be re-found)"""
import sys, time, itertools as it, numpy as np, torch
from h24_lugsearch import lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64); torch.set_num_threads(4)
def fib(n):
    k=np.arange(n)+0.5; th=np.arccos(1-2*k/n); ph=(np.pi*(1+5**0.5)*k)%(2*np.pi); return np.c_[th,ph]
def run(orb,NA,NS,NPOL,t0):
    f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
    A=2*np.pi*np.arange(NA)/NA; S=fib(NS)
    AA=np.array(list(it.product(A,A,A)))                     # [NA^3,3]
    SS=np.array(list(it.product(range(NS),range(NS),range(NS))))  # [NS^3,3]
    th_t=S[SS][:,:,0]; ph_t=S[SS][:,:,1]                      # [NS^3,3]
    best_v=[]; best_x=[]; n=0; vmin=np.inf
    for a in AA:
        th=np.c_[np.tile(a,(len(SS),1)),th_t,ph_t]
        v=lam(torch.tensor(th),Tf,cf).numpy(); n+=len(v); vmin=min(vmin,v.min())
        k=np.argsort(v)[:max(1,NPOL//len(AA)+2)]; best_v+=list(v[k]); best_x+=list(th[k])
    best_v=np.array(best_v); best_x=np.array(best_x); order=np.argsort(best_v)[:NPOL]
    x=torch.tensor(best_x[order],requires_grad=True)
    o2=torch.optim.LBFGS([x],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-18)
    def clo():
        o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
    o2.step(clo); vp=lam(x,Tf,cf).detach().numpy(); j=int(np.argmin(vp))
    print(f'orbit {orb} facet {f}: grid {NA}^3 phases x {NS}^3 frames = {n} points, grid min {vmin:.6e}; polished {len(vp)}: '
          f'min {vp[j]:.9e}, below -1e-7: {(vp<-1e-7).sum()}; params {np.round(x.detach().numpy()[j],4).tolist()}  {time.time()-t0:.0f}s',flush=True)
if __name__=='__main__':
    t0=time.time(); NA,NS,NPOL=int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
    for orb in [int(a) for a in sys.argv[1].split(',')]: run(orb,NA,NS,NPOL,t0)
