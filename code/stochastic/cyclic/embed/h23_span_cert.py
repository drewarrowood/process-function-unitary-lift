"""Round 23 (H.30.1), checker A: exact LP-duality certificates that a facet holds on Valid ∩ S, where S is the span of
Lemma H.30.1 (h23_span.py) for a family (comp:i = phase-process component i of H.29.3; rule:i = time-reversed PF lifts on refined PF i).
For each facet f (integer values valsI on the 744 PFs; rational functional g, exact on all PFs) we find, in exact rationals,
nu >= 0 (64) and lam (64) with  B^T (g - nu - Aeq^T lam) = 0  (B = integer basis of S)  and  sum(lam) + g_64 = t.
Then for every p in Valid ∩ S:  g.p + g_64 = nu.p + lam.(Aeq p) + g_64 = nu.p >= 0.   usage: fam1,fam2,...  [orbits]"""
import sys, itertools as it, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
from h23_span import span_gens, opat_comp, opat_rule, B3
from h20_common import valsI, canon, PF
import sympy as sp
oid=lambda b:4*b[0]+2*b[1]+b[2]
Aeq=[[0]*64 for _ in range(64)]
for r,f in enumerate(it.product(range(4),repeat=3)):
    for i in range(8): Aeq[r][8*i+oid([[0,1,B3[i][k],1-B3[i][k]][f[k]] for k in range(3)])]=1
AeqN=np.array(Aeq,float)
X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
# Valid's affine hull equals the PFs' affine hull (so the functional is determined on Valid by its PF values)
assert np.linalg.matrix_rank(X.astype(float))==38 and 64-np.linalg.matrix_rank(AeqN)==37
def functional(f):
    v=[int(x) for x in valsI[:,f]]; g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]
    gq=[Fr(x).limit_denominator(10**4) for x in g]
    assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744)); return gq
def rref_solve(A,b,guess):
    """exact solution of A x = b (Fractions); free variables set to the rationalised guess"""
    m=len(A); n=len(A[0]); M=[A[r][:]+[b[r]] for r in range(m)]; piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,m) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; inv=1/M[r][c]; M[r]=[x*inv for x in M[r]]
        for i in range(m):
            if i!=r and M[i][c]!=0: fct=M[i][c]; M[i]=[a-fct*bb for a,bb in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==m: break
    assert all(all(x==0 for x in M[i][:n]) and M[i][n]==0 for i in range(r,m)), 'inconsistent'
    x=[Fr(gv).limit_denominator(10**6) for gv in guess]
    for i,c in enumerate(piv): x[c]=0
    for i in reversed(range(len(piv))):
        c=piv[i]; x[c]=M[i][n]-sum(M[i][j]*x[j] for j in range(n) if j!=c and M[i][j]!=0)
    return x
def certify(fam,orbs):
    kind,ci=fam.split(':'); ci=int(ci)
    G=span_gens((lambda z,zp:opat_comp(ci,z,zp)) if kind=='comp' else (lambda z,zp:opat_rule(ci,z,zp)))
    _,piv=sp.Matrix(G.T.tolist()).rref(); Bz=G[list(piv)].T.astype(int); d=Bz.shape[1]; Bf=Bz.astype(float)
    ok=0; fails=[]; bound={}
    for f in [int(x) for x in np.where(np.isin(canon,orbs))[0]]:
        g=functional(f); gf=np.array([float(x) for x in g])
        lp=linprog(Bf.T@gf[:64],A_ub=-Bf,b_ub=np.zeros(64),A_eq=AeqN@Bf,b_eq=np.ones(64),bounds=[(None,None)]*d,method='highs')
        nu=-lp.ineqlin.marginals; lam=lp.eqlin.marginals      # c = -Bf^T(-nu) ... : Bf^T g = Bf^T nu + (Aeq Bf)^T lam
        J=[j for j in range(64) if nu[j]>1e-9]; opt=lp.fun+gf[64]; t=Fr(0) if abs(opt)<1e-9 else Fr(opt).limit_denominator(1000)
        if t<0: fails.append((f,'LP<0',opt)); continue
        # unknowns: nu_J, lam (64).  equations: Bz^T(nu_J) + Bz^T Aeq^T lam = Bz^T g ; sum lam = -g64
        A=[]; b=[]
        for c in range(d):
            A.append([Fr(int(Bz[j,c])) for j in J]+[Fr(sum(int(Bz[q,c])*Aeq[r][q] for q in range(64))) for r in range(64)])
            b.append(sum(int(Bz[q,c])*g[q] for q in range(64)))
        A.append([Fr(0)]*len(J)+[Fr(1)]*64); b.append(t-g[64]); bound[f]=t
        try: x=rref_solve(A,b,list(nu[J])+list(lam))
        except AssertionError: fails.append((f,'inconsistent')); continue
        nuJ=x[:len(J)]; lamx=x[len(J):]
        if min(nuJ,default=0)<0: fails.append((f,'nu<0')); continue
        # independent re-verification of the identity in p-space against every basis column
        nuv=[Fr(0)]*64
        for j,v in zip(J,nuJ): nuv[j]=v
        res=[g[q]-nuv[q]-sum(lamx[r] for r in range(64) if Aeq[r][q]) for q in range(64)]
        assert all(sum(res[q]*int(Bz[q,c]) for q in range(64))==0 for c in range(d)) and sum(lamx)+g[64]==t and t>=0
        ok+=1
    print(fam,'dim S',d,'facets certified',ok,'bounds',sorted(set(str(v) for v in bound.values())),'failed',len(fails),fails[:5],flush=True); return ok,fails
if __name__=='__main__':
    orbs=[int(a) for a in sys.argv[2].split(',')] if len(sys.argv)>2 else [28,54,57,66,69,75,81]
    for fam in sys.argv[1].split(','): certify(fam,orbs)
