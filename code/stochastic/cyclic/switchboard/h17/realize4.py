"""H.17.16 part (2)/(3) [NUMERICAL]: try to REALISE 4-class Klein-cluster boards.  Take random tclose4 jobs (family KC, k=4),
let the LOOSENED solver produce a board structure (P_o, class) compatible with the per-pair pattern supports, then solve for
the real class parameters (V = p0 + i sum p_m H(g_m), p a real unit vector, all |p_m| >= 0.05) minimising the Pauli-rule
residual (H.8.1) by least squares from several starts.  A realised board (residual < 1e-20, >= 4 distinct unitaries up to left
Paulis) is tested against all 29,344 PF-hull facets over all source states, and SH_grp^r (H.17.11a) is evaluated."""
import sys, json, random, numpy as np
from scipy.optimize import least_squares
import tclose4 as T4
from lib3 import PM, HM, FORB, pauli_coeffs, rule_residual, load_facets, facet_viol, px
seed=int(sys.argv[1]); NJ=int(sys.argv[2]); T4.BUDGET=int(sys.argv[3]) if len(sys.argv)>3 else T4.BUDGET; random.seed(seed); rng=np.random.default_rng(seed)
Tf,_=load_facets()
def supp_of(K,tol=1e-9): c=pauli_coeffs(K); return [s for s in range(64) if abs(c[s])>tol]
def _span(xs):
    H={0}
    for x in xs: H|={h^x for h in H}
    return H
def shgrp_r(U):
    best=None
    for r in range(8):
        W=np.einsum('oij,kj->oik',U,U[r].conj()); rep={}; a={}
        for o in range(8):
            for q in sorted(set(rep.values())):
                xs={px(s) for s in supp_of(W[o]@W[q].conj().T)}
                if len(xs)==1: rep[o]=q; a[o]=xs.pop(); break
            else: rep[o]=o; a[o]=0
        H={q:_span({px(s) for s in supp_of(W[q])}) for q in set(rep.values())}
        bad=sum(1 for o in range(8) for q in range(o+1,8) if rep[o]!=rep[q] and
                any(((a[o]^a[q]^h^h2)&(o^q))==(o^q) for h in H[rep[o]] for h2 in H[rep[q]]))
        if best is None or bad<best: best=bad
    return best
reps,_=T4.klein_reps()
def mkV(g,p): return p[0]*np.eye(8)+sum(1j*p[m+1]*HM[g[m]] for m in range(len(g)))
def build(cls,board,theta):
    ps=[]; i=0
    for g in cls:
        v=theta[i:i+len(g)+1]; i+=len(g)+1; ps.append(v/np.linalg.norm(v))
    V=[mkV(g,p) for g,p in zip(cls,ps)]
    return np.array([PM[P]@V[c] for P,c in board]),ps
def resid(theta,cls,board):
    U,ps=build(cls,board,theta); r=[]
    for o in range(8):
        for q in range(o+1,8):
            c=pauli_coeffs(U[o]@U[q].conj().T)[FORB[o^q]]; r+=list(c.real)+list(c.imag)
    for p in ps: r+=list(np.maximum(0,0.05-np.abs(p))*10)
    return np.array(r)
def ndistinct(U):
    R=[]
    for o in range(8):
        if not any((np.abs(pauli_coeffs(U[o]@U[q].conj().T))>1e-7).sum()==1 for q in R): R.append(o)
    return len(R)
JC={}
stats=dict(jobs=0,struct=0,realised=0,realised_ge4=0,best_facet=-1.)
for t in range(NJ):
    K=random.choice(reps)
    if K not in JC: JC[K]=T4.gen_jobs(K,4)
    job=random.choice(JC[K]); stats['jobs']+=1
    r=T4.solve(job,loosen='hard')
    if r is None: stats['no_hard_struct']=stats.get('no_hard_struct',0)+1
    if r=='UNRESOLVED': stats['unres']=stats.get('unres',0)+1
    if not r or r=='UNRESOLVED': continue
    stats['struct']+=1; cls=[tuple(c) for c in job['cls']]; board=[tuple(x) for x in r['board']]
    npar=sum(len(g)+1 for g in cls); best=None
    for s in range(6):
        sol=least_squares(resid,rng.normal(size=npar),args=(cls,board),xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
        f=float(np.sum(sol.fun**2))
        if best is None or f<best[0]: best=(f,sol.x)
        if f<1e-24: break
    if best[0]<1e-20:
        U,_=build(cls,board,best[1]); nd=ndistinct(U); stats['realised']+=1
        S={(o,q):[x for x in range(64) if abs(pauli_coeffs(U[o]@U[q].conj().T)[x])>1e-9] for o in range(8) for q in range(8) if o!=q}
        last=any(all(S[(o,o^(1<<j))]==[0] for o in range(8)) for j in range(3))
        first=any(all((((x&7)|(x>>3))>>j)&1==0 for v_ in S.values() for x in v_) for j in range(3))
        hard=not(last or first); stats['hard_realised']=stats.get('hard_realised',0)+hard
        if nd>=4 and hard:
            stats['realised_ge4']+=1; v=float(facet_viol(U,Tf).max()); stats['best_facet']=max(stats['best_facet'],v)
            print('REALISED HARD nd',nd,'shgrp_r_bad',shgrp_r(U),'facet',v,'rule',rule_residual(U),json.dumps(dict(cls=cls,board=board)),flush=True)
            np.savez('r4_%d_%d.npz'%(seed,t),U=U,cls=json.dumps(cls),board=json.dumps(board),viol=v)
            if v>1e-6: print('VIOLATION',v,flush=True)
    if t%5==0: print(t,json.dumps(stats),flush=True)
print('final',json.dumps(stats),flush=True)
