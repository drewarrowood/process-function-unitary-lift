"""Round 27 (H.34.6) checker A for an exact face certificate (h27_exact.py JSON[.gz]):
Q_S = sum_b E_b N_b G_b N_b^T E_b^T (N_b integer, G_b Gaussian-rational Hermitian, E_b = basis indices of weight block b).
Checks (Fractions throughout): G_b Hermitian; the identity p(psi,xi,u) - gamma |psi|^2 prod|xi|^2 = sum_S v_S^dag Q_S v_S coefficient by
coefficient, with p from h26_hsos.poly (rational T, c) and the Round-26 key rule; G_b positive definite via fraction-free elimination of
the real form [[Re,-Im],[Im,Re]].  Then Q_S >= 0, so p >= gamma*|psi|^2 prod|xi_k|^2 for |u_k| = 1, i.e. facet value >= gamma.
usage: cert.json[.gz]"""
import sys, json, gzip, math, numpy as np
from fractions import Fraction as F
from flint import fmpz
import h26_hsos as H
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); orb=C['orbit']; gam=F(C['gamma']); f=int(np.where(H.canon==orb)[0][0])
Tq=np.array([[F(x).limit_denominator(10**4) for x in row] for row in H.Tn[f,:64].reshape(8,8)],dtype=object)
cq=F(H.Tn[f,64]).limit_denominator(10**4)
assert max(abs(float(Tq[i,j])-H.Tn[f,8*i+j]) for i in range(8) for j in range(8))<1e-13 and abs(float(cq)-H.Tn[f,64])<1e-13
P,N=H.poly(Tq,cq); B=H.basis(); n=len(B)
def key(S,r,s):
    (z,a,m),(w,b,mp)=B[r],B[s]; xi=[];xb=[]
    for k in range(3):
        ak,bk=H.B3[a][k],H.B3[b][k]
        if (S>>k)&1: xi.append(ak); xb.append(bk)
        else: xi.append(bk); xb.append(ak)
    return (z,w,tuple(xi),tuple(xb),tuple(mp[k]-m[k] for k in range(3)))
def posdef(M):
    M=[row[:] for row in M]; m=len(M); prev=fmpz(1)
    for k in range(m):
        if M[k][k]<=0: return False
        for i in range(k+1,m):
            for j in range(k+1,m): M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return True
res={k:[F(v),F(0)] for k,v in P.items()}
for k,v in N.items(): res.setdefault(k,[F(0),F(0)])[0]-=gam*F(v)
npd=0; dims=0
for bl in C['blocks']:
    S=bl['S']; idx=bl['basis']; Nm=bl['N']; d=len(Nm[0]) if Nm and Nm[0] else 0
    if d==0: continue
    Gr=[[F(x) for x in r] for r in bl['Gr']]; Gi=[[F(x) for x in r] for r in bl['Gi']]
    assert all(Gr[i][j]==Gr[j][i] and Gi[i][j]==-Gi[j][i] for i in range(d) for j in range(d)), 'G not Hermitian'
    L=1
    for r in Gr+Gi:
        for x in r: L=math.lcm(L,x.denominator)
    R=[[fmpz(int((Gr[i][j] if i<d and j<d else Gr[i-d][j-d] if i>=d and j>=d else -Gi[i][j-d] if i<d else Gi[i-d][j])*L)) for j in range(2*d)] for i in range(2*d)]
    assert posdef(R), ('G not PD', S, bl['wt']); npd+=1; dims+=d
    # Q = N G N^T  (N integer)
    NG_r=[[sum(Nm[r][i]*Gr[i][j] for i in range(d) if Nm[r][i]) for j in range(d)] for r in range(len(idx))]
    NG_i=[[sum(Nm[r][i]*Gi[i][j] for i in range(d) if Nm[r][i]) for j in range(d)] for r in range(len(idx))]
    for r in range(len(idx)):
        for s in range(len(idx)):
            qr=sum(NG_r[r][j]*Nm[s][j] for j in range(d) if Nm[s][j]); qi=sum(NG_i[r][j]*Nm[s][j] for j in range(d) if Nm[s][j])
            if qr or qi:
                k=key(S,idx[r],idx[s]); e=res.setdefault(k,[F(0),F(0)]); e[0]-=qr; e[1]-=qi
bad=[k for k,(a,b) in res.items() if a or b]
print(f'orbit {orb}: {npd} blocks exactly PD (face dim {dims}); identity residual: {len(bad)} nonzero coefficients of {len(res)}')
assert not bad
print(f'orbit {orb}: PROVED (checker A) facet value >= {gam}')
