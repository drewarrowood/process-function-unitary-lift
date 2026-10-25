"""Round 17 (H.24.4): exact verification of the intersected lifted relaxation for any MODE produced by h17_lift_scs.py
(links A-B and A-C, link keys ('link', L, x, c); family A carries +K for every link, family L != A carries -K for its own).
Adapted from h16_liftAB_verify.py (Round 16).  Input: /tmp/r17/lift_{MODE}.pkl.  Every real parameter of every Hermitian multiplier (family multipliers
and the linking multipliers Lam_{x,c}) is rounded to the grid 2^-30, so all multipliers are exactly Hermitian dyadic matrices.
The maps 1 - T_q (Pauli twirl), the identity and the linking maps K^L (qubit permutation, kron 1_2, factor 1/2) are applied exactly
in integers at scale 2^64; C_v is replaced by C'_v exactly as in h12_lift_verify.py (Round 14).  For each cone a dyadic t with
S - t*1 > 0 is certified by Sylvester's criterion (Bareiss).  Identity, for any Hermitian multipliers and any feasible pair:
  y_A.P = sum_{L=A,B} ( sum Tr Lam^L + sum_v Tr[S^L_v Z^L_v] ) + sum_v Tr[(C_v - C'_v) Z^A_v]
        >= sum_L ( sum Tr Lam^L + 16 sum_{xM,xN} min_v t^L_v ) - 10^-12,
because sum_v Tr[K^A_v Z^A_v] = sum Tr[Lam F^A] = sum Tr[Lam F^B] = sum_v Tr[K^B_v Z^B_v] on the intersection.  [EXACT-CERTIFIED]"""
import pickle, sys, os, itertools as it, numpy as np, mpmath as mp
from fractions import Fraction as Fr
from multiprocessing import Pool
mp.mp.dps=60
os.environ['LIFTP']='0'
exec(open('/workspace/pful-graded/code/stochastic/cyclic/embed/h12_lift_common.py').read())
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
if LIFTP:   # relabel parties exactly as h12_lift_common does for psi
    Wq2={}
    for o in range(8):
        R,I=Wq[o]; R2=np.zeros((8,8),dtype=object); I2_=np.zeros((8,8),dtype=object)
        for a_ in range(8):
            for b_ in range(8): R2[pidx(a_),pidx(b_)]=R[a_,b_]; I2_[pidx(a_),pidx(b_)]=I[a_,b_]
        Wq2[pidx(o)]=(R2,I2_)
    Wq=Wq2
# consistency: W' agrees with the float W of h12_lift_common to 1e-15
assert max(abs(np.array(Wq[o][0],float)/2**63+1j*np.array(Wq[o][1],float)/2**63-W[o]).max() for o in range(8))<1e-14
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
D=pickle.load(open(sys.argv[1] if len(sys.argv)>1 else '/tmp/r17/lift_ABC.pkl','rb')); X=D['x']; OFF=D['off']; FAM=D['FAM']
G30=2**30; FS=SC//G30
def herm(key):   # exact Hermitian (R,I) at scale SC from the rounded parameters, ordering as hbasis() in h16_liftAB_scs.py
    o,n=OFF[key]; p=[int(round(t*G30))*FS for t in X[o:o+n*n]]
    R=np.zeros((n,n),dtype=object); I=np.zeros((n,n),dtype=object); k=0
    for i in range(n):
        for j in range(i,n):
            if i==j: R[i,i]=p[k]; k+=1
            else: R[i,j]=R[j,i]=p[k]; I[i,j]=p[k+1]; I[j,i]=-p[k+1]; k+=2
    return R,I
B3l=B3
def embQ(first):
    Q=np.zeros((16,16),dtype=object)
    for a in range(8):
        for g in (0,1):
            t=B3l[a]; dst=(t[0],g,t[1],t[2]) if first==0 else (g,t[0],t[1],t[2]); Q[int(''.join(map(str,dst)),2),a*2+g]=1
    return Q
QE=[embQ(0),embQ(1)]; I2o=np.eye(2,dtype=int).astype(object)
def famperm(L):
    perm=[L]+[j for j in range(3) if j!=L]
    orig=lambda t:tuple(t[perm.index(j)] for j in range(3))
    return orig,np.array([B3l.index(orig(B3l[a])) for a in range(8)])
def Kmap(RI,xl,qidx):
    out=[]
    for M in RI:
        E=QE[xl].dot(np.kron(M[np.ix_(qidx,qidx)],I2o)).dot(QE[xl].T)
        assert all(e%2==0 for e in E.ravel()); out.append(E//2)
    return out
def Sv(L,v):
    orig,qidx=famperm(L); c0,c1,xm,xn,cm,cn=v
    if L==0: R,I=Cq(*v)
    else: R=np.zeros((16,16),dtype=object); I=np.zeros((16,16),dtype=object)
    kb=(c0,c1,xn,cn); kc=(c0,c1,xm,cm)
    terms=[(herm(('Lam',L,xm,xn)),-1),(twi(herm(('G1',L,c0,xm,xn,cm,cn)),1),-1),(twi(herm(('G0',L,c1,xm,xn,cm,cn)),0),-1)]
    terms+= [(twi(herm(('GB',L)+kb),2),-1),(herm(('DB',L)+kb),+1)] if xm==0 else [(herm(('DB',L)+kb),-1)]
    terms+= [(twi(herm(('GC',L)+kc),3),-1),(herm(('DC',L)+kc),+1)] if xn==0 else [(herm(('DC',L)+kc),-1)]
    sg=1 if L==0 else -1
    for Lp in (FAM[1:] if L==0 else [L]):
        for xl,cl in ((0,c0),(1,c1)):
            xo=orig((xl,xm,xn)); co=orig((cl,cm,cn))
            terms.append((Kmap(herm(('link',Lp,B3l.index(xo),16*co[0]+4*co[1]+co[2])),xl,qidx),sg))
    for (a,b),s in terms: R=R+s*a; I=I+s*b
    return R,I
def posdef(M):
    A=[list(r) for r in M]; n=len(A); prev=1
    for k in range(n):
        if A[k][k]<=0: return False
        for i in range(k+1,n):
            for j in range(k+1,n): A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])//prev
        prev=A[k][k]
    return True
def cert(Lv):
    L,v=Lv; R,I=Sv(L,v); lam=np.linalg.eigvalsh(np.array(R,float)/SC+1j*np.array(I,float)/SC)[0]
    for marg in (1e-8,1e-6,1e-4):
        tn=int(np.floor((lam-marg)*2**24)); shift=tn*(SC//2**24); Rs=R.copy()
        for i in range(16): Rs[i,i]-=shift
        M=[[*Rs[i],*(-I[i])] for i in range(16)]+[[*I[i],*Rs[i]] for i in range(16)]
        if posdef(M): return L,v,Fr(tn,2**24),lam
    raise RuntimeError(f'no certificate for {Lv}')
if __name__=='__main__':
    V=list(it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)))
    with Pool(int(sys.argv[2]) if len(sys.argv)>2 else 3) as P: res=P.map(cert,[(L,v) for L in FAM for v in V],chunksize=16)
    bound=Fr(0)
    for L in FAM:
        trL=sum(Fr(int(sum(herm(('Lam',L)+k)[0][i,i] for i in range(16))),SC) for k in it.product((0,1),(0,1)))
        part=trL
        for xm,xn in it.product((0,1),(0,1)):
            sel=[r for r in res if r[0]==L and r[1][2]==xm and r[1][3]==xn]
            m=min(r[2] for r in sel); part+=16*m
            print(f'family {"ABC"[L]} (xM,xN)=({xm},{xn}): min_v t_v = {float(m):.9f} (float min eig {min(r[3] for r in sel):.3e})',flush=True)
        print(f'family {"ABC"[L]}: sum Tr Lam (rounded) = {float(trL):.9f}, contribution {float(part):.9f}',flush=True); bound+=part
    err=16*4*16*YMAX*2*2**-61; assert err<1e-12
    bound-=Fr(1,10**12)
    print('CERTIFIED (exact integer arithmetic): min over all instruments of y_A.P >=',bound,'~',float(bound))
