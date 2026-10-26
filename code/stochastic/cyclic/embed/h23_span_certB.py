"""Round 23 (H.30.1), checker B: an independent exact verification of the bounds of checker A (h23_span_cert.py).
Independent in every step: (i) S is rebuilt from different generators (phase components: o-classes from an integer basis of ker M;
rules: indicators of the differing blocks' outputs and of the equal-bit inputs), and its orthogonal complement N is computed exactly;
(ii) the facet functional g is solved exactly (DomainMatrix over QQ) from 38 affinely independent PFs and checked on all 744;
(iii) the LP is posed in p-space,  min g.p + g64  s.t.  Aeq p = 1,  N^T p = 0,  p >= 0,  and solved by the interior-point method;
(iv) the certificate g = Aeq^T lam + N mu + nu, nu >= 0, sum(lam) + g64 = t >= 0 is solved and checked coordinate-wise in exact rationals.
Then for every p in Valid ∩ S:  g.p + g64 = t + nu.p >= t >= 0.   usage: fam1,fam2,... [orbits]"""
import sys, json, itertools as it, numpy as np, sympy as sp
from fractions import Fraction as Fr
from sympy.polys.matrices import DomainMatrix
from sympy import QQ
from scipy.optimize import linprog
from h20_common import B3, others, valsI, canon, PF
from h22_phaseproc import MONO
C=json.load(open('h22_pp_components.json')); MAXI=[tuple(map(tuple,p)) for p in json.load(open('h20_fwd_enum.json'))['maximal']]
bit=lambda x,k:(x>>(2-k))&1          # same convention as B3 (B3[x][k]), checked below
assert all(bit(x,k)==B3[x][k] for x in range(8) for k in range(3))
mono=np.array([[[int(all(bit(o,a) for a in m[0]) and all(bit(z,b) for b in m[1])) for m in MONO] for z in range(8)] for o in range(8)])
def kerZ(M):
    out=[]
    for v in sp.Matrix(M).nullspace():
        den=sp.ilcm(*[sp.fraction(t)[1] for t in v]); out.append([int(t*den) for t in v])
    return np.array(out,dtype=np.int64).T
def igens(z,zp):
    S=[k for k in range(3) if bit(z,k)==bit(zp,k)]; D=[k for k in range(3) if k not in S]; out=[]
    for b in it.product((0,1),repeat=len(S)):
        out.append(np.array([int(all(bit(i,k)==bb for k,bb in zip(S,b)))*(-1)**sum(bit(i,k) for k in D) for i in range(8)]))
    return out
def ogens_comp(K):
    def f(z,zp):
        key={}
        for o in range(8): key.setdefault(tuple((mono[o,zp]-mono[o,z])@K),[]).append(o)
        return [np.array([int(o in c) for o in range(8)]) for c in key.values()]
    return f
def ogens_rule(parts):
    def f(z,zp):
        D=[k for k in range(3) if parts[k][others(k,z)]!=parts[k][others(k,zp)]]
        return [np.array([int(all(bit(o,k)==bb for k,bb in zip(D,b))) for o in range(8)]) for b in it.product((0,1),repeat=len(D))]
    return f
def S_perp(og):
    G=np.unique(np.array([np.outer(pi,po).ravel() for z in range(8) for zp in range(8) for po in og(z,zp) for pi in igens(z,zp)]),axis=0)
    Dm=DomainMatrix([[QQ(int(x)) for x in r] for r in G.tolist()],G.shape,QQ)
    N=Dm.nullspace().to_Matrix()          # rows span S^perp
    return np.array(N.tolist(),dtype=object), int(Dm.rank())
oid=lambda b:4*b[0]+2*b[1]+b[2]
Aeq=np.zeros((64,64),dtype=np.int64)
for r,f in enumerate(it.product(range(4),repeat=3)):
    for i in range(8): Aeq[r,8*i+oid([[0,1,bit(i,k),1-bit(i,k)][f[k]] for k in range(3)])]=1
X=np.c_[PF.reshape(744,-1),np.ones(744,int)].astype(np.int64)
# 38 affinely independent PF rows (greedy, exact)
sel=[]; cur=DomainMatrix([[QQ(0)]*65],(1,65),QQ); rk=0
for r in range(744):
    T=DomainMatrix([[QQ(int(x)) for x in X[q]] for q in sel+[r]],(len(sel)+1,65),QQ)
    if T.rank()>rk: sel.append(r); rk+=1
    if rk==38: break
XS=DomainMatrix([[QQ(int(x)) for x in X[q]] for q in sel],(38,65),QQ)
def functional(f):
    v=DomainMatrix([[QQ(int(valsI[q,f]))] for q in sel],(38,1),QQ)
    A=XS.hstack(v).rref()[0].to_Matrix(); g=[sp.Rational(0)]*65
    for row in range(38):
        c=next(j for j in range(65) if A[row,j]!=0); g[c]=A[row,65]/A[row,c]
    g=[Fr(int(x.p),int(x.q)) for x in g]
    assert all(sum(g[j]*int(X[q,j]) for j in range(65) if X[q,j])==int(valsI[q,f]) for q in range(744)); return g
def solveQ(A,b):
    """one exact solution of A x = b with free variables 0 (DomainMatrix rref)"""
    m,n=len(A),len(A[0]); Mx=DomainMatrix([[QQ(x.numerator,x.denominator) for x in A[r]]+[QQ(b[r].numerator,b[r].denominator)] for r in range(m)],(m,n+1),QQ)
    R,piv=Mx.rref(); R=R.to_Matrix()
    if n in piv: return None
    x=[Fr(0)]*n
    for row,c in enumerate(piv): x[c]=Fr(int(sp.fraction(R[row,n])[0]),int(sp.fraction(R[row,n])[1]))
    return x
def certify(fam,orbs):
    kind,ci=fam.split(':'); ci=int(ci)
    N,d=S_perp(ogens_comp(kerZ(np.array(C[ci]['rows']))) if kind=='comp' else ogens_rule(MAXI[ci]))
    Nq=[[Fr(int(sp.fraction(x)[0]),int(sp.fraction(x)[1])) for x in r] for r in N.tolist()]; Nf=np.array([[float(x) for x in r] for r in Nq]).reshape(-1,64)
    ok=0; fails=[]; bounds=set()
    for f in [int(x) for x in np.where(np.isin(canon,orbs))[0]]:
        g=functional(f); gf=np.array([float(x) for x in g[:64]])
        Ae=np.r_[Aeq.astype(float),Nf]; be=np.r_[np.ones(64),np.zeros(len(Nf))]
        lp=linprog(gf,A_eq=Ae,b_eq=be,bounds=[(0,None)]*64,method='highs-ipm')
        opt=lp.fun+float(g[64]); t=Fr(0) if abs(opt)<1e-8 else Fr(opt).limit_denominator(1000)
        if t<0: fails.append((f,'LP<0',opt)); continue
        nu=lp.lower.marginals; J=[j for j in range(64) if nu[j]>1e-7]
        # unknowns lam(64), mu(len N), nu_J ; equations: Aeq^T lam + N^T mu + nu = g (64 coords), sum lam = t - g64
        nN=len(Nq); A=[]; b=[]
        for q in range(64):
            A.append([Fr(int(Aeq[r,q])) for r in range(64)]+[Nq[s][q] for s in range(nN)]+[Fr(int(j==q)) for j in J]); b.append(g[q])
        A.append([Fr(1)]*64+[Fr(0)]*(nN+len(J))); b.append(t-g[64])
        x=solveQ(A,b)
        if x is None: fails.append((f,'inconsistent')); continue
        lam,mu,nuJ=x[:64],x[64:64+nN],x[64+nN:]
        if min(nuJ,default=0)<0:
            # free variables at 0 gave nu<0: retry with the support of the nonzero primal entries complemented (strict complementarity)
            fails.append((f,'nu<0')); continue
        nuv=[Fr(0)]*64
        for j,v in zip(J,nuJ): nuv[j]=v
        assert all(sum(lam[r]*int(Aeq[r,q]) for r in range(64))+sum(mu[s]*Nq[s][q] for s in range(nN))+nuv[q]==g[q] for q in range(64))
        assert sum(lam)+g[64]==t and t>=0 and min(nuv)>=0
        ok+=1; bounds.add(str(t))
    print(fam,'dim S',d,'facets certified',ok,'bounds',sorted(bounds),'failed',len(fails),fails[:5],flush=True)
if __name__=='__main__':
    orbs=[int(a) for a in sys.argv[2].split(',')] if len(sys.argv)>2 else [28,54,57,66,69,75,81]
    for fam in sys.argv[1].split(','): certify(fam,orbs)
