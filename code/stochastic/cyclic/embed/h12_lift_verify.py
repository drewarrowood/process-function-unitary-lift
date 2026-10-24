"""Exact verification of the lifted-A lower bound on min y_A.P for H.12 (Round 14, H.21.8).  Input: numerical dual /tmp/r14/lift_dual.pkl
(h12_lift_dual.py).  Every multiplier is rounded to a Gaussian dyadic (denominator 2^30) and made exactly Hermitian; twirls are exact.
The cost C_v (entries in Q(i,sqrt2)) is replaced by C'_v built exactly from W'_o = psi_o psi_o^dag evaluated with 60-digit mpmath and
rounded to the grid 2^-62; then 2^64 * S_v is a Gaussian-integer matrix.  For each v a dyadic t_v with S_v - t_v*1 > 0 is CERTIFIED by
Sylvester's criterion on the 32x32 real form (all leading principal minors > 0, computed exactly by Bareiss fraction-free elimination).
Identity (any Hermitian multipliers, any feasible Z of h12_lift.py, which contains every product of POVMs, hence every instrument by H.15.7d):
   y_A.P = sum Tr Lam + sum_v Tr[S_v Z_v] + sum_v Tr[(C_v - C'_v) Z_v]
         >= sum Tr Lam + 16 sum_{xB,xC} min_v t_v - 16*4*max_v ||C_v - C'_v||_op,
using Z_v >= 0 and sum_{v at fixed (xB,xC)} Tr Z_v = Tr 1_16 = 16.  The last term is bounded crudely and covered by subtracting 10^-12."""
import pickle, sys, itertools as it, numpy as np, mpmath as mp
from fractions import Fraction as Fr
from multiprocessing import Pool
mp.mp.dps=60
exec(open('/workspace/pful-graded/code/stochastic/cyclic/embed/h12_lift_common.py').read())
D=pickle.load(open(sys.argv[1] if len(sys.argv)>1 else '/tmp/r14/lift_dual.pkl','rb'))
SC=2**64
def gi(A,den):   # complex float matrix -> Gaussian integer pair at scale SC, rounded on grid 1/den, exactly Hermitian (average)
    Re=np.round(A.real*den).astype(object); Im=np.round(A.imag*den).astype(object)
    Re=np.vectorize(int,otypes=[object])(Re); Im=np.vectorize(int,otypes=[object])(Im)
    f=SC//(2*den); return ((Re+Re.T)*f,(Im-Im.T)*f)
def twi(A,q):    # exact: A - T_q(A), T_q(A) = 1/2 1_q (x) Tr_q A (entries scaled by SC; SC divisible by 2 many times)
    R,I=A; out=[]
    for M in (R,I):
        T=np.zeros((16,16),dtype=object)
        for i in range(16):
            for j in range(16):
                bi=(i>>(3-q))&1; bj=(j>>(3-q))&1
                if bi!=bj: continue
                s=0
                for t in (0,1):
                    ii=i^((bi^t)<<(3-q)); jj=j^((bj^t)<<(3-q)); s+=M[ii,jj]
                assert s%2==0; T[i,j]=s//2
        out.append(M-T)
    return tuple(out)
# exact-ish W' on the 2^-62 grid
Hs=mp.matrix(8,8)
for a in range(8):
    for b in range(8): Hs[a,b]=(-1)**par(a&b)/mp.sqrt(8)
phm=mp.matrix([0,0,0,1/mp.sqrt(2),(1-1j)/2,0,0,0])
Wq={}
for o in range(8):
    Dg=mp.diag([mp.mpc(1j)**MT[o][z] for z in range(8)]); p=Hs*Dg*Hs*phm
    R=np.zeros((8,8),dtype=object); I=np.zeros((8,8),dtype=object)
    for a in range(8):
        for b in range(8):
            e=p[a]*mp.conj(p[b]); R[a,b]=int(mp.nint(e.real*2**62)); I[a,b]=int(mp.nint(e.imag*2**62))
    R=(R+R.T)//1; I=(I-I.T)//1   # symmetrise: now 2x the value on grid 2^-62, i.e. value on grid 2^-63
    Wq[o]=(R,I)   # value = (R + iI)/2^63
yi=np.vectorize(int,otypes=[object])(np.round(y).astype(int)); assert np.allclose(yi.astype(float),y); YMAX=int(np.abs(y).max())
def embq(Wp,first):
    out=[]
    for M in Wp:
        W6=M.reshape(2,2,2,2,2,2)
        E=np.zeros((2,)*8,dtype=object)
        for g in (0,1):
            if first==0: E[:,g,:,:,:,g,:,:]=W6
            else: E[g,:,:,:,g,:,:,:]=W6
        out.append(E.reshape(16,16))
    return out
def Cq(cA0,cA1,xb,xc,cB,cC):   # 2^64 * C'_v  (C'_v = sum w/2 * emb(W'), W' = (R+iI)/2^63)
    (aB,oB),(aC,oC)=pc(cB),pc(cC); R=np.zeros((16,16),dtype=object); I=np.zeros((16,16),dtype=object)
    for xa,cA,first in ((0,cA0,0),(1,cA1,1)):
        aA,oA=pc(cA); w=yi[B3.index((xa,xb,xc)),B3.index((aA,aB,aC))]
        if w:
            e=embq(Wq[B3.index((oA,oB,oC))],first)
            R=R+w*e[0]; I=I+w*e[1]     # factor: 2^64 * (1/2) * 2^-63 = 1
    return (R,I)
DEN=2**30
def H(A): return gi(np.asarray(A),DEN)
Lam={k:H(v) for k,v in D['Lam'].items()}
def mt(d,q): return {k:twi(H(v),q) for k,v in d.items()}
G1=mt(D['G1'],1); G0=mt(D['G0'],0); GB=mt(D['GB'],2); GC=mt(D['GC'],3)
DB={k:H(v) for k,v in D['DB'].items()}; DC={k:H(v) for k,v in D['DC'].items()}
def Sv(v):
    cA0,cA1,xb,xc,cB,cC=v; R,I=Cq(*v)
    terms=[(Lam[xb,xc],-1),(G1[cA0,xb,xc,cB,cC],-1),(G0[cA1,xb,xc,cB,cC],-1)]
    kb=(cA0,cA1,xc,cC); kc=(cA0,cA1,xb,cB)
    terms+= [(GB[kb],-1),(DB[kb],+1)] if xb==0 else [(DB[kb],-1)]
    terms+= [(GC[kc],-1),(DC[kc],+1)] if xc==0 else [(DC[kc],-1)]
    for (a,b),s in terms: R=R+s*a; I=I+s*b
    return R,I
def posdef(M):   # Bareiss on integer symmetric matrix: all leading principal minors > 0
    A=[list(r) for r in M]; n=len(A); prev=1
    for k in range(n):
        if A[k][k]<=0: return False
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])//prev
        prev=A[k][k]
    return True
def cert(v):
    R,I=Sv(v); Rf=np.array(R,float)/SC; If=np.array(I,float)/SC
    lam=np.linalg.eigvalsh(Rf+1j*If)[0]
    for marg in (1e-8,1e-6,1e-4):
        tn=int(np.floor((lam-marg)*2**24)); shift=tn*(SC//2**24)
        Rs=R.copy()
        for i in range(16): Rs[i,i]-=shift
        M=[[*Rs[i],*(-I[i])] for i in range(16)]+[[*I[i],*Rs[i]] for i in range(16)]
        if posdef(M): return v,Fr(tn,2**24),lam
    raise RuntimeError(f'no certificate for {v}')
if __name__=='__main__':
    V=list(it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)))
    with Pool(int(sys.argv[2]) if len(sys.argv)>2 else 2) as P: res=P.map(cert,V,chunksize=16)
    trL=sum(Fr(int(sum(Lam[k][0][i,i] for i in range(16))),SC) for k in Lam)
    print('sum Tr Lam (rounded) =',float(trL),flush=True)
    bound=trL
    for xb,xc in it.product((0,1),(0,1)):
        m=min(t for v,t,l in res if v[2]==xb and v[3]==xc); ml=min(l for v,t,l in res if v[2]==xb and v[3]==xc)
        print(f'(xB,xC)=({xb},{xc}): min_v t_v = {float(m):.9f}  (float min eig {ml:.3e})',flush=True); bound+=16*m
    # ||C-C'||_op <= ||C-C'||_F <= 16 * (2*YMAX/2) * (entry error of W' <= 2^-61 per part) * sqrt(2)  -- far below 1e-12
    err=16*4*16*YMAX*2*2**-61
    assert err<1e-12
    bound-=Fr(1,10**12)
    print('max |y| =',YMAX,'crude rounding error term',err)
    print('CERTIFIED (exact integer arithmetic): min over all instruments of y_A.P >=',bound,'~',float(bound))
