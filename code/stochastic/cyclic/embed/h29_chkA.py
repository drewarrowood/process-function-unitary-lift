"""Round 29 (H.36) checker A for an exact level-K certificate (h27_exact.py run on an h29_export.py problem; JSON[.gz]).
The certificate lists, per weight block b, its monomials v_b (exponent vectors [psi(8), psibar(8), xi(6), xibar(6), u(3)]),
an integer matrix N_b and a Gaussian-rational Hermitian G_b.  Claimed identity (Laurent polynomials in u, |u_k| = 1):
    |xi_K|^2 (p - gamma |psi|^2 prod_k |xi_k|^2) = sum_b v_b^dag N_b G_b N_b^T v_b .
Here p is taken from h26_hsos.poly (the Round-26 coefficient table, NOT the h29 export) and converted to exponent vectors, then
multiplied by |xi_K|^2 = |xi_K0|^2 + |xi_K1|^2.  All arithmetic in Fractions; G_b PD by fraction-free elimination of the real form
[[Re,-Im],[Im,Re]].  Any monomial vector v gives v^dag Q v >= 0, so on |xi_k| = 1 the facet value is >= gamma.
usage: cert.json[.gz]"""
import sys, json, gzip, math, numpy as np
from fractions import Fraction as F
from flint import fmpz
import h26_hsos as H
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); orb=C['orbit']; gam=F(C['gamma']); f=int(np.where(H.canon==orb)[0][0])
lev=C.get('level','0'); K=int(lev[2:]) if lev.startswith('K=') else None
Tq=np.array([[F(x).limit_denominator(10**4) for x in row] for row in H.Tn[f,:64].reshape(8,8)],dtype=object)
cq=F(H.Tn[f,64]).limit_denominator(10**4)
assert max(abs(float(Tq[i,j])-H.Tn[f,8*i+j]) for i in range(8) for j in range(8))<1e-13 and abs(float(cq)-H.Tn[f,64])<1e-13
P26,N26=H.poly(Tq,cq)
def conv(key):   # (z psibar, w psi, xi party-indices, xibar party-indices, u-exponents) -> exponent vectors
    z,w,xi,xb,d=key; a=[0]*8; ab=[0]*8; x=[0]*6; xbv=[0]*6
    a[w]+=1; ab[z]+=1
    for k in range(3): x[2*k+xi[k]]+=1; xbv[2*k+xb[k]]+=1
    return (tuple(a),tuple(ab),tuple(x),tuple(xbv),tuple(int(t) for t in d))
def mulK(D):
    if K is None: return D
    R={}
    for m,v in D.items():
        for b in (0,1):
            x=list(m[2]); xb=list(m[3]); x[2*K+b]+=1; xb[2*K+b]+=1; k=(m[0],m[1],tuple(x),tuple(xb),m[4]); R[k]=R.get(k,0)+v
    return R
P={};NV={}
for k,v in P26.items(): kk=conv(k); P[kk]=P.get(kk,0)+F(v)
for k,v in N26.items(): kk=conv(k); NV[kk]=NV.get(kk,0)+F(v)
P=mulK(P); NV=mulK(NV)
res={k:[v,F(0)] for k,v in P.items()}
for k,v in NV.items(): res.setdefault(k,[F(0),F(0)])[0]-=gam*v
def posdef(M):
    M=[row[:] for row in M]; m=len(M); prev=fmpz(1)
    for k in range(m):
        if M[k][k]<=0: return False
        for i in range(k+1,m):
            for j in range(k+1,m): M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return True
npd=0; dims=0
for bl in C['blocks']:
    Nm=bl['N']; d=len(Nm[0]) if Nm and Nm[0] else 0
    if d==0: continue
    mono=[tuple(tuple(x) for x in m) for m in bl['mono']]; assert len(mono)==len(Nm)
    Gr=[[F(x) for x in r] for r in bl['Gr']]; Gi=[[F(x) for x in r] for r in bl['Gi']]
    assert all(Gr[i][j]==Gr[j][i] and Gi[i][j]==-Gi[j][i] for i in range(d) for j in range(d)), 'G not Hermitian'
    L=1
    for r in Gr+Gi:
        for x in r: L=math.lcm(L,x.denominator)
    R=[[fmpz(int((Gr[i][j] if i<d and j<d else Gr[i-d][j-d] if i>=d and j>=d else -Gi[i][j-d] if i<d else Gi[i-d][j])*L)) for j in range(2*d)] for i in range(2*d)]
    assert posdef(R), ('G not PD', bl['S'], bl['wt']); npd+=1; dims+=d
    n=len(Nm)
    NGr=[[sum(Nm[r][i]*Gr[i][j] for i in range(d) if Nm[r][i]) for j in range(d)] for r in range(n)]
    NGi=[[sum(Nm[r][i]*Gi[i][j] for i in range(d) if Nm[r][i]) for j in range(d)] for r in range(n)]
    for r in range(n):
        mr=mono[r]; cr=(mr[1],mr[0],mr[3],mr[2],tuple(-t for t in mr[4]))   # conj(v_r)
        for s in range(n):
            qr=sum(NGr[r][j]*Nm[s][j] for j in range(d) if Nm[s][j]); qi=sum(NGi[r][j]*Nm[s][j] for j in range(d) if Nm[s][j])
            if qr or qi:
                k=tuple(tuple(x+y for x,y in zip(a,b)) for a,b in zip(cr,mono[s])); e=res.setdefault(k,[F(0),F(0)]); e[0]-=qr; e[1]-=qi
bad=[k for k,(a,b) in res.items() if a or b]
print(f'orbit {orb} level {lev}: {npd} blocks exactly PD (face dim {dims}); identity residual: {len(bad)} nonzero coefficients of {len(res)}')
assert not bad
print(f'orbit {orb}: PROVED (checker A) facet value >= {gam}  [identity multiplied by |xi_{K}|^2; |xi_k|=1 on the domain]')
