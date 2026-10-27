"""Round 24 (H.31.2): numerical sanity check of the orbit-invariance argument: minimise EVERY facet of the given orbits over rule-4
phase boards (exact parametrisation of h24_lugsearch, NS starts each, Adam then best-of-batch).  Expected: no value below -1e-9.
usage: orbits NS seed"""
import sys, numpy as np, torch, time
from h24_lugsearch import lam
from h20_common import Tn, canon
orbs=[int(a) for a in sys.argv[1].split(',')]; NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3])); t0=time.time()
for orb in orbs:
    fs=np.where(canon==orb)[0]; worst=(1,None)
    for f in fs:
        Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
        th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
        for it_ in range(800):
            opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
            if it_==500:
                for g in opt.param_groups: g['lr']=0.005
        m=float(lam(th,Tf,cf).min())
        if m<worst[0]: worst=(m,int(f))
    print(f'orbit {orb}: {len(fs)} facets x {NS} starts; min over all {worst[0]:.3e} (facet {worst[1]})  {time.time()-t0:.0f}s',flush=True)
