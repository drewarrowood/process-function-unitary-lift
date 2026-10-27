"""Round 26 (H.33.4) checker B, independent of h26_hsos.poly and of checker A's coefficient rules and PD test.
Rebuilds p by formal polynomial arithmetic: amplitude A_io = sum_z conj(f_i[z]) u^{o.x(z)} psi_z with conj(e_0)=(xb0,xb1),
conj(e_1)=(-x1, x0); p = sum T[i,o] conj(A_io) A_io + c |psi|^2 prod_k(x_k0 xb_k0 + x_k1 xb_k1), u ubar = 1.
Rebuilds each v_S monomial explicitly as an exponent vector and multiplies conj(v_r) v_s.  Residual exact (Fractions).
PD of Zr_S + 2^tauexp_S I (real form) via FLINT fmpz_mat.fflu: identity permutation and positive leading minors (Sylvester).
Also recomputes max_w n_m(w) for the |v_S|^2 bound.  usage: cert.npz"""
import sys, numpy as np, itertools as it
from fractions import Fraction as F
from flint import fmpz_mat
from h23_span import MAXI
from h20_common import Tn, canon, B3, others
C=np.load(sys.argv[1]); Zr,Zi,K,TJ,orb=C['Zr'],C['Zi'],int(C['K']),C['tauexp'],int(C['orb'])
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
n=len(basis); assert Zr.shape==(8,n,n)
nm=max(sum(1 for (w,b,m) in basis if w==w0 and b==0) for w0 in range(8))
res=dict(p); den=F(1,2**K)
for S in range(8):
    V=[]
    for (w,b,m) in basis:
        xi=[0]*6; xb=[0]*6
        for k in range(3):
            if (S>>k)&1: xb[2*k+B3[b][k]]+=1
            else: xi[2*k+B3[b][k]]+=1
        V.append((-1,w,tuple(xi),tuple(xb),tuple(m)))
    for r_ in range(n):
        cr=conjp({V[r_]:(F(1),F(0))}); (mr,_),=cr.items()
        for s_ in range(n):
            ms=V[s_]; m=(mr[0],ms[1],tuple(x+y for x,y in zip(mr[2],ms[2])),tuple(x+y for x,y in zip(mr[3],ms[3])),tuple(x+y for x,y in zip(mr[4],ms[4])))
            a,bb=res.get(m,(F(0),F(0))); res[m]=(a-int(Zr[S,r_,s_])*den,bb-int(Zi[S,r_,s_])*den)
r1=sum(abs(a)+abs(b) for a,b in res.values())
assert all(np.array_equal(Zr[S],Zr[S].T) and np.array_equal(Zi[S],-Zi[S].T) for S in range(8))
tot=F(0)
for S in range(8):
    j=int(TJ[S]); tau=F(2)**j; A=Zr[S].astype(object)+int(tau*2**K)*np.eye(n,dtype=object)
    R=np.block([[A,-Zi[S].astype(object)],[Zi[S].astype(object),A]])
    P,L,D,U=fmpz_mat([[int(x) for x in row] for row in R]).fflu()
    ok=P==fmpz_mat([[int(i==j_) for j_ in range(2*n)] for i in range(2*n)]) and all(U[i,i]>0 for i in range(2*n))
    print(f' S={S}: tau=2^{j}, fflu identity perm and positive leading minors: {ok}',flush=True); assert ok; tot+=tau
delta=nm*tot+r1
print(f'orbit {orb}: checker B: n_m max {nm}, residual L1 {float(r1):.3e}, PROVED facet value >= -{float(delta):.3e}')
