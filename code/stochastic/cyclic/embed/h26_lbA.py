"""Round 26 (H.33.4) checker A: exact lower bound from a numerical Hermitian SOS Gram set (h26_qspec.py output).
Steps: (1) project Q onto the coefficient identity in floating point (each Gram entry belongs to exactly one key, so the
projection spreads each key's residual evenly over its entries), Hermitise, round to Gaussian dyadics Z[i]/2^K;
(2) exact residual r = p - sum_S v_S^dag Qr_S v_S with rational T (Fractions), r1 = sum_key (|Re r|+|Im r|);
(3) for each S a dyadic tau_S with Qr_S + tau_S I positive definite, proved by exact fraction-free elimination of the real
352x352 form [[A,-B],[B,A]] (all pivots > 0).  For unit psi, unit spinors, |u_k|=1: |v_S|^2 = sum_w |psi_w|^2 n_m(w) <= 4 and every
monomial has modulus <= 1, hence  facet value = min p >= -(4 sum_S tau_S + r1).   usage: orbit q.npz [cert_out.npz]  (writes the rounded certificate: integer Gram numerators over 2^K and tau exponents)"""
import sys, numpy as np, itertools as it
from fractions import Fraction as F
from flint import fmpz
import h26_hsos as H
orb=int(sys.argv[1]); f=int(np.where(H.canon==orb)[0][0]); K=48
Tq=np.array([[F(x).limit_denominator(10**4) for x in row] for row in H.Tn[f,:64].reshape(8,8)],dtype=object)
cq=F(H.Tn[f,64]).limit_denominator(10**4)
assert max(abs(float(Tq[i,j])-H.Tn[f,8*i+j]) for i in range(8) for j in range(8))<1e-13 and abs(float(cq)-H.Tn[f,64])<1e-13
P,N=H.poly(Tq,cq); B=H.basis(); n=len(B)
Q=np.load(sys.argv[2])['Q']
def key(S,r,s):
    (z,a,m),(w,b,mp)=B[r],B[s]; xi=[];xb=[]
    for k in range(3):
        ak,bk=H.B3[a][k],H.B3[b][k]
        if (S>>k)&1: xi.append(ak); xb.append(bk)
        else: xi.append(bk); xb.append(ak)
    return (z,w,tuple(xi),tuple(xb),tuple(mp[k]-m[k] for k in range(3)))
KEYS=[[[key(S,r,s) for s in range(n)] for r in range(n)] for S in range(8)]
# (1) float projection
acc={};cnt={}
for S in range(8):
    for r in range(n):
        for s in range(n):
            k=KEYS[S][r][s]; acc[k]=acc.get(k,0)+Q[S,r,s]; cnt[k]=cnt.get(k,0)+1
for S in range(8):
    for r in range(n):
        for s in range(n):
            k=KEYS[S][r][s]; Q[S,r,s]+=(complex(P.get(k,0))-acc[k])/cnt[k]
Q=(Q+np.conj(np.transpose(Q,(0,2,1))))/2
for k in P:
    if k not in cnt: print('key not covered by basis', k, P[k])
Zr=np.round(Q.real*2**K).astype(np.int64); Zi=np.round(Q.imag*2**K).astype(np.int64)
Zr=np.triu(Zr)+np.transpose(np.triu(Zr,1),(0,2,1)); Zi=np.triu(Zi,1)-np.transpose(np.triu(Zi,1),(0,2,1))
# (2) exact residual
sr={k:F(0) for k in P}; si={k:F(0) for k in P}
for k,v in P.items(): sr[k]=F(v)
for S in range(8):
    for r in range(n):
        for s in range(n):
            k=KEYS[S][r][s]
            sr[k]=sr.get(k,F(0))-F(int(Zr[S,r,s]),2**K); si[k]=si.get(k,F(0))-F(int(Zi[S,r,s]),2**K)
r1=sum(abs(sr[k])+abs(si.get(k,0)) for k in sr)
print(f'orbit {orb}: basis {n}, K={K}, exact residual L1 r1 = {float(r1):.3e}',flush=True)
# (3) tau_S
def posdef(M):   # fraction-free Gaussian elimination, integer symmetric M (list of lists of fmpz): all pivots > 0
    M=[row[:] for row in M]; m=len(M); prev=fmpz(1)
    for k in range(m):
        if M[k][k]<=0: return False
        for i in range(k+1,m):
            for j in range(k+1,m): M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return True
tot=F(0); TJ=[]
for S in range(8):
    lam=np.linalg.eigvalsh(Zr[S]/2**K+1j*Zi[S]/2**K)[0]; j=int(np.floor(np.log2(max(-lam,1e-13))))+2; tau=F(1,2**(-j)) if j<0 else F(2**j)
    A=Zr[S]+int(tau*2**K)*np.eye(n,dtype=np.int64); Bm=Zi[S]
    R=np.block([[A,-Bm],[Bm,A]]); ok=posdef([[fmpz(int(x)) for x in row] for row in R])
    print(f' S={S}: float lambda_min {lam:.2e}, tau = 2^{j}, exact PD: {ok}',flush=True); assert ok; tot+=tau; TJ.append(j)
delta=4*tot+r1
if len(sys.argv)>3: np.savez_compressed(sys.argv[3],Zr=Zr,Zi=Zi,K=K,tauexp=np.array(TJ),orb=orb)
print(f'orbit {orb}: PROVED (checker A) facet value >= -{float(delta):.3e}  (4*sum tau = {float(4*tot):.3e}, r1 = {float(r1):.3e})')
