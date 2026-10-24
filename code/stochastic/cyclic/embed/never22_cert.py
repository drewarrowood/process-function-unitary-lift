"""Round 15, H.22.2: exact certificate that a pure board violates a never-crossed facet (orbit 14 or 25).
Usage: python3 never22_cert.py <params.npy> <global facet index> [denominator]
1. The 3 node unitaries U_k and the 6 frames of never22_lugU.py are replaced by exactly unitary matrices with Gaussian-rational
   entries via the Cayley transform U = w (1 + iK)(1 - iK)^{-1} (w in {1,i,-1,-i}), K Hermitian with rational entries rounded from the float optimum.
2. V (64x64, Gaussian rationals) is checked exactly unitary; the source psi is a Gaussian-rational vector.
3. p(i|o) = sum_f |<i f|V|o psi>|^2 / <psi|psi> is computed exactly (rationals); exact validity (64+8 equalities) and positivity checked.
4. The facet functional is rationalised and checked exactly against the integer facet values on all 744 PFs (as in validcert.py);
   its exact value at p is negative.  [PROVED: exact rational arithmetic]  Purity of the board: VOKB fleshing-out [CITED] + numerical."""
import sys, itertools as it, numpy as np, gzip
from fractions import Fraction as Fr
par=np.load(sys.argv[1]); fi=int(sys.argv[2]); D=int(sys.argv[3]) if len(sys.argv)>3 else 1000
rev=int(par[0]); th=par[1:]
B3=list(it.product((0,1),repeat=3)); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
# --- Gaussian rationals as (re,im) Fraction pairs
def cm(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
Z0=(Fr(0),Fr(0)); O1=(Fr(1),Fr(0))
def mm(A,B):
    n,k,m=len(A),len(B),len(B[0]); C=[[Z0]*m for _ in range(n)]
    for i in range(n):
        Ai=A[i]
        for l in range(k):
            a=Ai[l]
            if a==Z0: continue
            Bl=B[l]; Ci=C[i]
            for j in range(m):
                b=Bl[j]
                if b!=Z0: Ci[j]=ca(Ci[j],cm(a,b))
    return C
def kron(A,B): return [[cm(A[i//len(B)][j//len(B[0])],B[i%len(B)][j%len(B[0])]) for j in range(len(A[0])*len(B[0]))] for i in range(len(A)*len(B))]
def inv2(M):
    (a,b),(c,d)=M; det=ca(cm(a,d),cm((-b[0],-b[1]),c)); n=det[0]**2+det[1]**2; di=(det[0]/n,-det[1]/n)
    return [[cm(d,di),cm((-b[0],-b[1]),di)],[cm((-c[0],-c[1]),di),cm(a,di)]]
def cayley_exact(U):
    # U = w * Cayley(K) with w in {1,i,-1,-i} chosen so that -1 is far from the spectrum of conj(w) U
    ws=[(1,0),(0,1),(-1,0),(0,-1)]; I=np.eye(2)
    wi=max(range(4),key=lambda j:np.abs(np.linalg.eigvals(np.conj(complex(*ws[j]))*U)+1).min())
    C=cayley_core(np.conj(complex(*ws[wi]))*U); w=(Fr(ws[wi][0]),Fr(ws[wi][1]))
    return [[cm(w,x) for x in r] for r in C]
def cayley_core(U):
    I=np.eye(2); K=1j*(I-U)@np.linalg.inv(I+U); K=(K+K.conj().T)/2
    q=lambda x:Fr(round(x*D),D)
    k00=(q(K[0,0].real),Fr(0)); k11=(q(K[1,1].real),Fr(0)); k01=(q(K[0,1].real),q(K[0,1].imag)); k10=(k01[0],-k01[1])
    Kq=[[k00,k01],[k10,k11]]
    iK=[[cm((Fr(0),Fr(1)),x) for x in r] for r in Kq]
    Am=[[ca(O1 if i==j else Z0,iK[i][j]) for j in range(2)] for i in range(2)]
    Bm=[[ca(O1 if i==j else Z0,(-iK[i][j][0],-iK[i][j][1])) for j in range(2)] for i in range(2)]
    return mm(Am,inv2(Bm))
def su2(t):
    a,b,c=t; return np.array([[np.cos(a)*np.exp(1j*b),np.sin(a)*np.exp(1j*c)],[-np.sin(a)*np.exp(-1j*c),np.cos(a)*np.exp(-1j*b)]])
def u2(t): return np.exp(1j*t[3])*su2(t[:3])
Uf=[u2(th[4*j:4*j+4]) for j in range(3)]; Ff=[su2(th[12+3*j:15+3*j]) for j in range(6)]
import os
MODE=os.environ.get('MODE','')
if MODE=='lugT':
    # Every optimised node unitary has eigenphase gap pi, so U_k = e^{i a_k} R_k X R_k^dag.  Then L_U = (R)_AI (D)_F L_X (R^dag)_P with
    # D an o-dependent phase on F, hence L_U^T = (Rbar)_F L_X^T (R^T)_AO (D)_P: the board is the time-reversed Lugano purification L_X^T
    # with input frames FI and output frames R_k^T FO_k (phases on F, P drop out of p).  Here the nodes are EXACTLY X.
    assert rev==1
    Rs=[]
    for U in Uf:
        ev,Q=np.linalg.eig(U); a=np.angle(ev[0]); Zd=ev*np.exp(-1j*a)
        assert abs(Zd[0]-1)<1e-4 and abs(Zd[1]+1)<1e-4, 'node unitary not a phase times a reflection'
        R=Q@np.array([[1,1],[1,-1]])/2**.5; assert abs(U-np.exp(1j*a)*R@np.array([[0,1],[1,0]])@R.conj().T).max()<1e-4; Rs.append(R)
    Ff=Ff[:3]+[Rs[k].T@Ff[3+k] for k in range(3)]
    Xq=[[Z0,O1],[O1,Z0]]; Uq=[Xq,Xq,Xq]; Uf=[np.array([[0,1],[1,0]],complex)]*3
    print('MODE lugT: nodes exactly X (board = frames . time-reversed Lugano purification . frames)')
else:
    Uq=[cayley_exact(U) for U in Uf]
Fq=[cayley_exact(U) for U in Ff]
tofl=lambda M:np.array([[float(x[0])+1j*float(x[1]) for x in r] for r in M])
print('max |exact - float| over the 9 qubit unitaries: %.2e'%max(abs(tofl(a)-b).max() for a,b in zip(Uq+Fq,Uf+Ff)))
I2=[[O1,Z0],[Z0,O1]]
def mpow(U,e): return U if e else I2
k3=lambda a,b,c:kron(kron(a,b),c)
Lm=[[Z0]*64 for _ in range(64)]
for o in range(8):
    e=lug(*B3[o]); g=k3(*[mpow(Uq[j],e[j]) for j in range(3)])
    for s in range(8):
        for i in range(8): Lm[8*i+o][8*o+s]=g[i][s]
if rev: Lm=[list(r) for r in zip(*Lm)]
I8=[[O1 if i==j else Z0 for j in range(8)] for i in range(8)]
V=mm(mm(kron(k3(*Fq[:3]),I8),Lm),kron(k3(*Fq[3:]),I8))
Vd=[[(V[j][i][0],-V[j][i][1]) for j in range(64)] for i in range(64)]
VV=mm(Vd,V); assert all(VV[i][j]==(O1 if i==j else Z0) for i in range(64) for j in range(64)); print('V is exactly unitary (Gaussian rationals)')
psi_f=np.load(sys.argv[1].replace('.npy','_psi.npy')) if len(sys.argv)>4 else None
# source: maximising eigenvector of the float facet operator, rounded
sys.argv=['x','1','0','0']
exec(open('never22_lugU.py').read().split('best=[]')[0].split("lug=lambda")[0])   # facet data only
W=tofl(V).reshape(8,8,8,8); P=np.einsum('ifos,ifot->iost',W.conj(),W).reshape(64,8,8)
Fm=np.einsum('r,rst->st',Tn[fi,:64],P)+Tn[fi,64]*np.eye(8); w,Ue=np.linalg.eigh(Fm); psi=Ue[:,0]; psi=psi/psi[np.argmax(abs(psi))]
print('float relative facet value with exact board: %.6f (orbit %d)'%(w[0],canon[fi]))
ps=[(Fr(round(x.real*D),D),Fr(round(x.imag*D),D)) for x in psi]; nn=sum(a*a+b*b for a,b in ps)
p=[[Fr(0)]*8 for _ in range(8)]   # p[i][o]
for o in range(8):
    for i in range(8):
        tot=Fr(0)
        for f in range(8):
            amp=Z0
            for s in range(8):
                v=V[8*i+f][8*o+s]
                if v!=Z0: amp=ca(amp,cm(v,ps[s]))
            tot+=amp[0]**2+amp[1]**2
        p[i][o]=tot/nn
assert all(x>=0 for r in p for x in r)
for o in range(8): assert sum(p[i][o] for i in range(8))==1
for f in it.product(range(4),repeat=3):
    assert sum(p[i][B3.index(tuple((f[t]>>B3[i][t])&1 for t in range(3)))] for i in range(8))==1
print('p is exactly a valid classical process (positivity, normalisation, 64 deterministic interventions)')
PFi=np.load('../pfs744.npy').astype(int); Zi=np.load('../../physics/facets/Z.npy').astype(int)
h=Hm[fi].astype(int); v=[int(x) for x in Zi@h[:37]+h[37]]
X=np.c_[PFi.reshape(744,-1),np.ones(744,int)]
g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]; gq=[Fr(x).limit_denominator(10**4) for x in g]
assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744)); print('facet functional exact on all 744 PFs; max PF value',max(v))
val=sum(gq[8*i+o]*p[i][o] for i in range(8) for o in range(8))+gq[64]
print('EXACT facet value at p:',val,'=',float(val),' relative:',float(val/max(v)))
assert val<0; print('CERTIFIED: facet %d (orbit %d) is violated by the classical process of a unitary board.'%(fi,canon[fi]))
