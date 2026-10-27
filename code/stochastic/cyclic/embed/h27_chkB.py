"""Round 27 (H.34.6) checker B for an exact face certificate (h27_exact.py JSON[.gz]); independent of h26_hsos.poly/basis, of the
export and of checker A.  p is rebuilt by formal polynomial arithmetic exactly as in h26_lbB.py (amplitudes A_io, conj(e_0)=(xb0,xb1),
conj(e_1)=(-x1,x0), u ubar = 1); v_S monomials rebuilt as exponent vectors; Q_b = N_b G_b N_b^T by FLINT fmpq_mat products;
residual p - gamma|psi|^2prod|xi|^2 - sum_S v_S^dag Q_S v_S must vanish identically; each G_b PD via FLINT fmpz_mat.fflu on the scaled
real form (identity permutation, positive leading minors = Sylvester).  usage: cert.json[.gz]"""
import sys, json, gzip, math, numpy as np, itertools as it
from fractions import Fraction as F
from flint import fmpz_mat, fmpq_mat, fmpq
from h23_span import MAXI
from h20_common import Tn, canon, B3, others
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); orb=int(C['orbit']); gam=F(C['gamma'])
f=int(np.where(canon==orb)[0][0]); X=[[MAXI[4][k][others(k,z)] for k in range(3)] for z in range(8)]
T=[[F(Tn[f,8*i+o]).limit_denominator(10**4) for o in range(8)] for i in range(8)]; c=F(Tn[f,64]).limit_denominator(10**4)
assert all(abs(float(T[i][o])-Tn[f,8*i+o])<1e-13 for i in range(8) for o in range(8))
# monomial: (psibar z or -1, psi w or -1, xi exps (6), xibar exps (6), u exps (3));  coefficients complex Fractions as (re,im)
def mul(a,b):
    out={}
    for ma,(ar,ai) in a.items():
        for mb,(br,bi) in b.items():
            assert not (ma[0]>=0 and mb[0]>=0) and not (ma[1]>=0 and mb[1]>=0)
            m=(max(ma[0],mb[0]),max(ma[1],mb[1]),tuple(x+y for x,y in zip(ma[2],mb[2])),tuple(x+y for x,y in zip(ma[3],mb[3])),tuple(x+y for x,y in zip(ma[4],mb[4])))
            r,i=out.get(m,(F(0),F(0))); out[m]=(r+ar*br-ai*bi,i+ar*bi+ai*br)
    return out
def conjp(a): return {(m[1],m[0],m[3],m[2],tuple(-e for e in m[4])):(r,-i) for m,(r,i) in a.items()}
def e6(k,a): v=[0]*6; v[2*k+a]=1; return tuple(v)
Z6=(0,)*6
p={}
for i in range(8):
    for o in range(8):
        A={}
        for z in range(8):
            xi=[0]*6; xb=[0]*6; s=1
            for k in range(3):
                b=B3[z][k]
                if B3[i][k]==0: xb[2*k+b]+=1
                else:
                    if b==0: s=-s; xi[2*k+1]+=1
                    else: xi[2*k+0]+=1
            m=(-1,z,tuple(xi),tuple(xb),tuple(B3[o][k]*X[z][k] for k in range(3)))
            r,_=A.get(m,(F(0),F(0))); A[m]=(r+s,F(0))
        for m,(r,im) in mul(conjp(A),A).items():
            pr,pi=p.get(m,(F(0),F(0))); p[m]=(pr+T[i][o]*r,pi+T[i][o]*im)
norm={(z,-1,Z6,Z6,(0,0,0)):(F(0),F(0)) for z in []}
psi2={}
for z in range(8): psi2[(z,z,Z6,Z6,(0,0,0))]=(F(1),F(0))
for k in range(3):
    psi2=mul(psi2,{(-1,-1,e6(k,0),e6(k,0),(0,0,0)):(F(1),F(0)),(-1,-1,e6(k,1),e6(k,1),(0,0,0)):(F(1),F(0))})
for m,(r,im) in psi2.items():
    pr,pi=p.get(m,(F(0),F(0))); p[m]=(pr+c*r,pi)
# basis, regenerated
basis=[(w,b,m) for w in range(8) for b in range(8) for m in it.product(*[range(X[w][k]+1) for k in range(3)])]
n=len(basis)
nm=max(sum(1 for (w,b,m) in basis if w==w0 and b==0) for w0 in range(8))
res=dict(p)
for m,(r,im) in psi2.items():
    pr,pi=res.get(m,(F(0),F(0))); res[m]=(pr-gam*r,pi)
V={}
for S in range(8):
    for t,(w,b,m) in enumerate(basis):
        xi=[0]*6; xb=[0]*6
        for k in range(3):
            if (S>>k)&1: xb[2*k+B3[b][k]]+=1
            else: xi[2*k+B3[b][k]]+=1
        V[S,t]=(-1,w,tuple(xi),tuple(xb),tuple(m))
toF=lambda q: F(int(q.p),int(q.q))
npd=0
for bl in C['blocks']:
    S=bl['S']; idx=bl['basis']; Nl=bl['N']; d=len(Nl[0]) if Nl and Nl[0] else 0
    if d==0: continue
    Gr=[[F(x) for x in r] for r in bl['Gr']]; Gi=[[F(x) for x in r] for r in bl['Gi']]
    L=1
    for r in Gr+Gi:
        for x in r: L=math.lcm(L,x.denominator)
    R=[[int((Gr[i][j] if i<d and j<d else Gr[i-d][j-d] if i>=d and j>=d else -Gi[i][j-d] if i<d else Gi[i-d][j])*L) for j in range(2*d)] for i in range(2*d)]
    assert all(R[i][j]==R[j][i] for i in range(2*d) for j in range(2*d))
    Pm,Lm,Dm,Um=fmpz_mat(R).fflu()
    ok=Pm==fmpz_mat([[int(i==j) for j in range(2*d)] for i in range(2*d)]) and all(Um[i,i]>0 for i in range(2*d))
    assert ok, ('G not PD',S,bl['wt']); npd+=1
    Nm=fmpq_mat(Nl); Qr=Nm*fmpq_mat([[fmpq(x.numerator,x.denominator) for x in r] for r in Gr])*Nm.transpose()
    Qi=Nm*fmpq_mat([[fmpq(x.numerator,x.denominator) for x in r] for r in Gi])*Nm.transpose()
    for a,ia in enumerate(idx):
        mr=V[S,ia]; mr=(mr[1],mr[0],mr[3],mr[2],tuple(-e for e in mr[4]))   # conj(v_r)
        for c_,ic in enumerate(idx):
            qr,qi=toF(Qr[a,c_]),toF(Qi[a,c_])
            if not (qr or qi): continue
            ms=V[S,ic]; m=(mr[0],ms[1],tuple(x+y for x,y in zip(mr[2],ms[2])),tuple(x+y for x,y in zip(mr[3],ms[3])),tuple(x+y for x,y in zip(mr[4],ms[4])))
            x0,y0=res.get(m,(F(0),F(0))); res[m]=(x0-qr,y0-qi)
bad=[m for m,(a,b) in res.items() if a or b]
print(f'orbit {orb}: checker B: {npd} blocks PD (fflu/Sylvester), {len(bad)} nonzero residual coefficients of {len(res)}')
assert not bad
print(f'orbit {orb}: PROVED (checker B) facet value >= {gam}')
