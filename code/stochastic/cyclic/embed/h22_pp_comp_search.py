"""Round 22 (H.29.3): facet search over each maximal valid component of three-qubit phase processes (h22_pp_components.json).
Inside a component validity is exact (x = N y), so no penalty is needed.  Minimise the Rayleigh quotient over (y, frames, psi);
report the exact minimum over psi (smallest eigenvalue).  Validity of the best point is re-checked with pen.  usage: ORBS seed NSTART"""
import sys, json, time, numpy as np, torch
from h22_copp import pen, facet_M
from h22_phaseproc import U_of
from h20_common import Tn, REP, canon
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
C=json.load(open('h22_pp_components.json'))
Ns=[]
for c in C:
    M=np.array(c['rows'],float); r=np.linalg.matrix_rank(M); _,_,Vt=np.linalg.svd(M); Ns.append(torch.tensor(Vt[r:].T))
ORBS=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NS=int(sys.argv[3]); rng=np.random.default_rng(seed); t0=time.time()
for orb in ORBS:
    f=REP[orb] if orb in REP else int(np.where(canon==orb)[0][0])
    Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); res=[]
    for ci,N in enumerate(Ns):
        best=(9,None); hits=0
        for r in range(NS):
            y=torch.tensor(np.r_[rng.uniform(-np.pi,np.pi,N.shape[1])*2,rng.uniform(-np.pi,np.pi,9)],requires_grad=True); ps=torch.tensor(rng.normal(size=16),requires_grad=True)
            opt=torch.optim.LBFGS([y,ps],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-15)
            X=lambda y: torch.cat([N@y[:N.shape[1]],y[N.shape[1]:]])
            def clo():
                opt.zero_grad(); U=U_of(X(y)); psi=torch.complex(ps[:8],ps[8:]); v=torch.vdot(psi,facet_M(U,Tf,cf)@psi).real/torch.vdot(psi,psi).real; v.backward(); return v
            try: opt.step(clo)
            except Exception: continue
            U=U_of(X(y.detach())); v=float(torch.linalg.eigvalsh(facet_M(U,Tf,cf))[0]); hits+=v<-1e-9
            if v<best[0]: best=(v,X(y.detach()).numpy(),float(pen(U)))
        res.append((best[0],hits,best[2] if best[1] is not None else None))
        if best[1] is not None and best[0]<-1e-9: np.save(f'/tmp/r22/ppc_o{orb}_c{ci}_s{seed}.npy',best[1])
    print(f'orbit {orb} facet {f}: per component (best, hits/{NS}, pen at best):',' '.join(f'c{ci}:{v:.3e}/{h}' for ci,(v,h,p) in enumerate(res)),
          f'| overall best {min(r[0] for r in res):.6e}, max pen at bests {max(r[2] for r in res if r[2] is not None):.1e}, {time.time()-t0:.0f}s',flush=True)
