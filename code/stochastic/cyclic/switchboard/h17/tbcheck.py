"""Tuned boards (tb_*.npz from nsearch2b, plus shp_11_3339.npy): (i) SH_grp with nsearch classes, (ii) SH_grp^r = SH_grp of
W_o = U_o U_r^dag with monomial grouping (H.17.11 theorem), best r, (iii) facet test max over source states,
(iv) explicit PF-blend LP over the 744 PFs at the worst-case source state and 3 random ones, with rational rounding."""
import sys,glob,json,numpy as np, itertools as it
from fractions import Fraction
from scipy.optimize import linprog
from lib3 import *
T,canon=load_facets()
def supp(K,tol=1e-9): c=pauli_coeffs(K); return [s for s in range(64) if abs(c[s])>tol]
def span(xs):
    H={0}
    for x in xs: H|={h^x for h in H}
    return H
def shgrp_r(U):
    best=None
    for r in range(8):
        W=np.einsum('oij,kj->oik',U,U[r].conj()); rep={}; a={}
        for o in range(8):
            for q in sorted(set(rep.values())):
                xs={px(s) for s in supp(W[o]@W[q].conj().T)}
                if len(xs)==1: rep[o]=q; a[o]=xs.pop(); break
            else: rep[o]=o; a[o]=0
        H={q:span({px(s) for s in supp(W[q])}) for q in set(rep.values())}
        bad=sum(1 for o in range(8) for q in range(o+1,8) if rep[o]!=rep[q] and
                any(((a[o]^a[q]^h^h2)&(o^q))==(o^q) for h in H[rep[o]] for h2 in H[rep[q]]))
        info=(bad,r,len(H),sorted(len(x) for x in H.values()))
        if best is None or bad<best[0]: best=info
    return best
PFf=PF.reshape(744,64)
def lp(p):
    n=744; c=np.r_[np.zeros(n),np.ones(128)]
    Aeq=np.c_[PFf.T,np.eye(64),-np.eye(64)]; Aeq=np.r_[Aeq,[np.r_[np.ones(n),np.zeros(128)]]]
    r=linprog(c,A_eq=Aeq,b_eq=np.r_[p,1],bounds=(0,None),method='highs')
    lam=r.x[:n]; fr=[Fraction(x).limit_denominator(10**12) for x in lam]; fr=[max(f,Fraction(0)) for f in fr]; S=sum(fr); fr=[f/S for f in fr]
    rec=np.array([float(sum(fr[t]*int(PFf[t,j]) for t in range(n) if fr[t])) for j in range(64)])
    return r.fun, int((lam>1e-12).sum()), np.abs(rec-p).max()
if __name__!="__main__": raise SystemExit  # library use stops here
rng=np.random.default_rng(0); out=[]
files=sorted(glob.glob('tb_*.npz'))+['shp_11_3339.npy']
for f in files:
    if f.endswith('.npy'): U=np.load(f); phi=None; meta={}
    else:
        d=np.load(f); U=d['U']; phi=d['phi']; meta=dict(shbad=int(d['shbad']),P=d['P'].tolist(),k=d['k'].tolist(),g=json.loads(str(d['g'])))
    row=dict(file=f,rule=float(rule_residual(U)))
    if meta:
        H=[span({px(x) for x in gg}) for gg in meta['g']]; P,k=meta['P'],meta['k']
        row['SH']=meta['shbad']; row['SHgrp']=sum(1 for o in range(8) for q in range(o+1,8) if k[o]!=k[q] and
            any(((px(P[o])^px(P[q])^h^h2)&(o^q))==(o^q) for h in H[k[o]] for h2 in H[k[q]]))
    row['SHgrp_r']=shgrp_r(U); row['facet_max']=float(facet_viol(U,T).max())
    Pm=projectors(U); lps=[]
    for v in ([phi] if phi is not None else [])+[ (lambda z:z/np.linalg.norm(z))(rng.normal(size=8)+1j*rng.normal(size=8)) for _ in range(3)]:
        p=np.einsum('s,rst,t->r',v.conj(),Pm,v).real
        lps.append(lp(p))
    row['lp_L1']=max(x[0] for x in lps); row['lp_support']=[x[1] for x in lps]; row['rational_resid']=max(x[2] for x in lps)
    print(json.dumps(row),flush=True); out.append(row)
print('SUMMARY n',len(out),'SHgrp_fail',sum(r.get('SHgrp',0)>0 for r in out),'SHgrp_r_fail',sum(r['SHgrp_r'][0]>0 for r in out),
      'max facet',max(r['facet_max'] for r in out),'max LP L1',max(r['lp_L1'] for r in out),'max rational resid',max(r['rational_resid'] for r in out))
