"""Round 29 (H.36) checker B for an exact level-K certificate; independent of h26_hsos, of h29_export.py and of checker A.
p is rebuilt by formal polynomial arithmetic as in h27_chkB.py (amplitudes A_io, conj(e_0)=(xb0,xb1), conj(e_1)=(-x1,x0)),
multiplied by |xi_K|^2 and converted to exponent vectors; Q_b = N_b G_b N_b^T by FLINT fmpq_mat products; the residual
|xi_K|^2(p - gamma|psi|^2prod|xi|^2) - sum_b v_b^dag Q_b v_b must vanish identically; each G_b PD via FLINT fmpz_mat.fflu on the
scaled real form (identity permutation, positive pivots = Sylvester).  usage: cert.json[.gz]"""
import sys, json, gzip, math, numpy as np
from fractions import Fraction as F
from flint import fmpz_mat, fmpq_mat, fmpq
from h23_span import MAXI
from h20_common import Tn, canon, B3, others
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); orb=int(C['orbit']); gam=F(C['gamma']); lev=C.get('level','0'); K=int(lev[2:]) if lev.startswith('K=') else None
f=int(np.where(canon==orb)[0][0]); X=[[MAXI[4][k][others(k,z)] for k in range(3)] for z in range(8)]
T=[[F(Tn[f,8*i+o]).limit_denominator(10**4) for o in range(8)] for i in range(8)]; c=F(Tn[f,64]).limit_denominator(10**4)
assert all(abs(float(T[i][o])-Tn[f,8*i+o])<1e-13 for i in range(8) for o in range(8))
# internal monomial: (psibar z or -1, psi w or -1, xi exps 6, xibar exps 6, u exps 3); complex Fraction coefficients (re,im)
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
Z6=(0,)*6; U0=(0,0,0)
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
psi2={(z,z,Z6,Z6,U0):(F(1),F(0)) for z in range(8)}
for k in range(3): psi2=mul(psi2,{(-1,-1,e6(k,0),e6(k,0),U0):(F(1),F(0)),(-1,-1,e6(k,1),e6(k,1),U0):(F(1),F(0))})
lhs=dict(p)
for m,(r,im) in psi2.items():
    pr,pi=lhs.get(m,(F(0),F(0))); lhs[m]=(pr+(c-gam)*r,pi+(c-gam)*im)
if K is not None: lhs=mul(lhs,{(-1,-1,e6(K,0),e6(K,0),U0):(F(1),F(0)),(-1,-1,e6(K,1),e6(K,1),U0):(F(1),F(0))})
def toexp(m):
    a=[0]*8; ab=[0]*8
    if m[1]>=0: a[m[1]]+=1
    if m[0]>=0: ab[m[0]]+=1
    return (tuple(a),tuple(ab),m[2],m[3],m[4])
res={}
for m,v in lhs.items():
    k=toexp(m); r0,i0=res.get(k,(F(0),F(0))); res[k]=(r0+v[0],i0+v[1])
toF=lambda q: F(int(q.p),int(q.q))
npd=0
for bl in C['blocks']:
    Nl=bl['N']; d=len(Nl[0]) if Nl and Nl[0] else 0
    if d==0: continue
    V=[tuple(tuple(x) for x in m) for m in bl['mono']]
    Gr=[[F(x) for x in r] for r in bl['Gr']]; Gi=[[F(x) for x in r] for r in bl['Gi']]
    L=1
    for r in Gr+Gi:
        for x in r: L=math.lcm(L,x.denominator)
    R=[[int((Gr[i][j] if i<d and j<d else Gr[i-d][j-d] if i>=d and j>=d else -Gi[i][j-d] if i<d else Gi[i-d][j])*L) for j in range(2*d)] for i in range(2*d)]
    assert all(R[i][j]==R[j][i] for i in range(2*d) for j in range(2*d)), 'G not Hermitian'
    Pm,Lm,Dm,Um=fmpz_mat(R).fflu()
    assert Pm==fmpz_mat([[int(i==j) for j in range(2*d)] for i in range(2*d)]) and all(Um[i,i]>0 for i in range(2*d)), ('G not PD',bl['S'],bl['wt']); npd+=1
    Nm=fmpq_mat(Nl); Qr=Nm*fmpq_mat([[fmpq(x.numerator,x.denominator) for x in r] for r in Gr])*Nm.transpose()
    Qi=Nm*fmpq_mat([[fmpq(x.numerator,x.denominator) for x in r] for r in Gi])*Nm.transpose()
    for a in range(len(V)):
        mr=V[a]; cr=(mr[1],mr[0],mr[3],mr[2],tuple(-e for e in mr[4]))
        for b in range(len(V)):
            qr,qi=toF(Qr[a,b]),toF(Qi[a,b])
            if not (qr or qi): continue
            k=tuple(tuple(x+y for x,y in zip(u,v)) for u,v in zip(cr,V[b])); x0,y0=res.get(k,(F(0),F(0))); res[k]=(x0-qr,y0-qi)
bad=[m for m,(a,b) in res.items() if a or b]
print(f'orbit {orb} level {lev}: checker B: {npd} blocks PD (fflu/Sylvester), {len(bad)} nonzero residual coefficients of {len(res)}')
assert not bad
print(f'orbit {orb}: PROVED (checker B) facet value >= {gam}')
