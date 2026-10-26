"""Round 23 (H.30.1): linear (affine-hull) constraints obeyed by the statistics of each valid phase-process component (H.29.3),
and the LP bound  min facet over Valid ∩ affine hull  for the open orbits.  If that LP minimum is >= 0, the facet holds on the
whole component (all phases, frames, sources), because the component's statistics lie in that set.
Step 1 (here, numerical): sample statistics, compute the affine hull dimension and the LP minima.  usage: NSAMP seed"""
import sys, json, itertools as it, numpy as np, torch
from scipy.optimize import linprog
from h22_phaseproc import U_of
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
C=json.load(open('h22_pp_components.json'))
NS=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2]))
B=[(a>>2&1,a>>1&1,a&1) for a in range(8)]; oid=lambda b:4*b[0]+2*b[1]+b[2]
# Valid: p[i,o] >= 0, sum_i p[i, f(i)] = 1 for the 64 deterministic interventions
fs=list(it.product(range(4),repeat=3)); Aeq=[]
for f in fs:
    row=np.zeros((8,8))
    for i in range(8):
        o=tuple((f[k]>>(1-B[i][k]))&1 if False else [0,1,B[i][k],1-B[i][k]][f[k]] for k in range(3)); row[i,oid(o)]=1
    Aeq.append(row.ravel())
Aeq=np.array(Aeq); beq=np.ones(64)
ORB=[26,30,31,28,54,57,66,69,75,81]; FAC={o:np.where(canon==o)[0] for o in ORB}
def sample(N):
    M=np.array(c['rows'],float) if False else None
def stats_of(x,psi):
    U=U_of(torch.tensor(x)).numpy(); a=np.einsum('ois,s->io',U,psi); return (np.abs(a)**2).ravel()
out={}
for ci,c in enumerate(C):
    M=np.array(c['rows'],float); r=np.linalg.matrix_rank(M); _,_,Vt=np.linalg.svd(M); N=Vt[r:].T
    P=[]
    for s in range(NS):
        y=rng.uniform(-np.pi,np.pi,N.shape[1])*3; x=np.r_[N@y,rng.uniform(-np.pi,np.pi,9)]
        psi=rng.normal(size=8)+1j*rng.normal(size=8); psi/=np.linalg.norm(psi); P.append(stats_of(x,psi))
    P=np.array(P); p0=P.mean(0); sv=np.linalg.svd(P-p0,compute_uv=False); d=int((sv>1e-9*sv[0]).sum())
    _,_,Vt2=np.linalg.svd(P-p0); Bas=Vt2[:d].T   # affine hull = p0 + span(Bas)
    res={}
    for o in ORB:
        mins=[]
        for f in FAC[o]:
            # variables a (d); p = p0 + Bas a ; constraints p>=0 and Aeq p = 1
            lp=linprog(Tn[f,:64]@Bas, A_ub=-Bas, b_ub=p0, A_eq=Aeq@Bas, b_eq=beq-Aeq@p0, bounds=[(None,None)]*d, method='highs')
            mins.append(lp.fun+Tn[f,:64]@p0+Tn[f,64] if lp.status==0 else np.nan)
        res[o]=float(np.nanmin(mins))
    out[ci]=dict(dim=d,res=res); print(ci,c['free'],'aff dim',d,' '.join(f'{o}:{v:.4g}' for o,v in res.items()),flush=True)
json.dump(out,open(f'h23_affhull_s{sys.argv[2]}.json','w'))
