"""Round 24 (H.31.2): a purity-based SDP relaxation for the Lugano-type families (level 1, "entrywise span + PSD").
For a time-reversed PF lift on rule w' (H.27.2) with source rho (mixed allowed) the statistics are p(i|o) = 1^T Z(i,o) 1, where
Z(i,o) = rho o G_{io} (Schur product), G_{io}[z,z'] = chi_{zz'}(o) prod_k conj(e_k[i_k,z_k]) e_k[i_k,z'_k].  Exact properties used:
  (P1) Z(i,o) is PSD (Schur product of PSD rho and the PSD G_{io} = Schur product of rank-one frame and PSD K factors);
  (P2) for every pair (z,z'), the 64-vector (i,o) -> Z_{zz'}(i,o) lies in the per-pair span (o-pattern) x (i-pattern) of Lemma H.30.1;
  (P3) sum_{z} sum_i Z_{zz}(i,o) = Tr rho = 1.
The relaxation minimises the facet over all Z satisfying (P1)-(P3).  It is a relaxation of the whole family (every K, frame, source),
so a minimum >= 0 proves the facet on the family; a negative minimum proves nothing.  usage: rules(comma) orbits(comma) [mode]"""
import sys, itertools as it, numpy as np, cvxpy as cp, time
from h23_span import opat_rule, opat_comp, ipat
from h20_common import Tn, canon
def pair_perp(opat):
    N={}
    for z in range(8):
        for zp in range(8):
            G=np.array([np.outer(pi,po).ravel() for po in opat(z,zp) for pi in ipat(z,zp)],float)
            u,s,vt=np.linalg.svd(G); r=int((s>1e-9).sum()); N[z,zp]=vt[r:]          # rows orthogonal to the span
    return N
def build(opat):
    N=pair_perp(opat)
    Z=[cp.Variable((8,8),hermitian=True) for _ in range(64)]          # index q = 8*i+o
    cons=[z>>0 for z in Z]
    for (z,zp),Nn in N.items():
        if zp<z or len(Nn)==0: continue
        v=cp.hstack([Z[q][z,zp] for q in range(64)])
        cons.append(Nn@v==0)
    for o in range(8): cons.append(sum(cp.real(cp.trace(Z[8*i+o])) for i in range(8))==1)
    return Z,cons
def solve(Z,cons,f,solver='CLARABEL'):
    obj=sum(Tn[f,q]*cp.real(cp.sum(Z[q])) for q in range(64) if Tn[f,q]!=0)+Tn[f,64]
    pr=cp.Problem(cp.Minimize(obj),cons); pr.solve(solver=solver); return pr.value,pr.status
if __name__=='__main__':
    fams=sys.argv[1].split(','); orbs=[int(a) for a in sys.argv[2].split(',')]; allf=len(sys.argv)>3 and sys.argv[3]=='all'
    for fam in fams:
        kind,ci=fam.split(':'); ci=int(ci); t0=time.time()
        Z,cons=build((lambda z,zp:opat_rule(ci,z,zp)) if kind=='rule' else (lambda z,zp:opat_comp(ci,z,zp)))
        for o in orbs:
            fs=np.where(canon==o)[0] if allf else [int(np.where(canon==o)[0][0])]
            vals=[solve(Z,cons,int(f)) for f in fs]
            m=min(v for v,s in vals); bad=sum(v<-1e-6 for v,s in vals)
            print(f'{fam} orbit {o}: facets {len(fs)} SDP min {m:.6e} below -1e-6: {bad} statuses {sorted(set(s for v,s in vals))} {time.time()-t0:.0f}s',flush=True)
