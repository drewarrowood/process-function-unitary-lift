"""Round 21 (H.28): exact certificate for a time-reversed PF lift point found by h20_trev_search.py.  usage: params.npy W ORB [DEN]
The board: refined PF w'=maxi[W], node unitaries U_{k,x} (D_k x D_k), prepared states phi_k(o), SU(2) input frames E_k, source psi.
p(i|o) = psi^dag G_io psi / |psi|^2,  G_io[a,b] = prod_k conj(E_k[a_k,i_k]) E_k[b_k,i_k] <U_{k,w_k(a)}phi_k(o_k), U_{k,w_k(b)}phi_k(o_k)>/|phi_k(o_k)|^2.
1. Every U_{k,x} and E_k is replaced by an EXACTLY unitary Gaussian-rational matrix (Cayley transform of a rationalised Hermitian K,
   times w in {1,i,-1,-i}); phi, psi are rounded to Gaussian rationals (denominator DEN).  Unitarity is checked exactly.
2. p is computed exactly; positivity, normalisation and the 64 deterministic local interventions are checked exactly.
3. The facet functional is rationalised and checked exactly on all 744 PFs; its exact value at p is reported.  [PROVED: exact arithmetic]"""
import sys, itertools as it, numpy as np, json
from fractions import Fraction as Fr
pf=sys.argv[1]; W=int(sys.argv[2]); ORB=int(sys.argv[3]); DEN=int(sys.argv[4]) if len(sys.argv)>4 else 10**6
src=open('h20_trev_search.py').read().split('rng=np.random')[0]
sys.argv=['x',str(W),'1','1',str(ORB)]; exec(src)
import torch
th=np.load(pf); parts=maxi[W]; nb=[max(p)+1 for p in parts]; D=[2*n for n in nb]
sizes=[nb[k]*2*D[k]*D[k]+2*2*D[k]+3 for k in range(3)]
xa=[[parts[k][others(k,a)] for a in range(8)] for k in range(3)]
Z0=(Fr(0),Fr(0)); O1=(Fr(1),Fr(0))
def cm(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def cc(a): return (a[0],-a[1])
def cdiv(a,b): n=b[0]**2+b[1]**2; return cm(a,(b[0]/n,-b[1]/n))
def mm(A,B):
    return [[ (lambda s: s)(sum_c([cm(A[i][l],B[l][j]) for l in range(len(B))])) for j in range(len(B[0]))] for i in range(len(A))]
def sum_c(L):
    r=Z0
    for x in L: r=ca(r,x)
    return r
def inv(M):
    n=len(M); A=[list(M[i])+[O1 if i==j else Z0 for j in range(n)] for i in range(n)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=Z0); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[cdiv(x,pv) for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=Z0:
                f=A[r][c]; A[r]=[ca(A[r][j],cm((-f[0],-f[1]),A[c][j])) for j in range(2*n)]
    return [r[n:] for r in A]
def q(x): return Fr(round(x*DEN),DEN)
def cayley_exact(U):
    n=U.shape[0]; I=np.eye(n); ws=[(1,0),(0,1),(-1,0),(0,-1)]
    wi=max(range(4),key=lambda j:np.abs(np.linalg.eigvals(np.conj(complex(*ws[j]))*U)+1).min())
    V=np.conj(complex(*ws[wi]))*U; K=1j*(I-V)@np.linalg.inv(I+V); K=(K+K.conj().T)/2
    Kq=[[(q(K[i,j].real),q(K[i,j].imag)) if i<j else None for j in range(n)] for i in range(n)]
    for i in range(n):
        Kq[i][i]=(q(K[i,i].real),Fr(0))
        for j in range(i): Kq[i][j]=cc(Kq[j][i])
    iK=[[cm((Fr(0),Fr(1)),x) for x in r] for r in Kq]
    Am=[[ca(O1 if i==j else Z0,iK[i][j]) for j in range(n)] for i in range(n)]
    Bm=[[ca(O1 if i==j else Z0,(-iK[i][j][0],-iK[i][j][1])) for j in range(n)] for i in range(n)]
    C=mm(Am,inv(Bm)); w=(Fr(ws[wi][0]),Fr(ws[wi][1]))
    return [[cm(w,x) for x in r] for r in C]
def is_unitary(U):
    n=len(U); Ud=[[cc(U[j][i]) for j in range(n)] for i in range(n)]; P=mm(Ud,U)
    return all(P[i][j]==(O1 if i==j else Z0) for i in range(n) for j in range(n))
tofl=lambda M:np.array([[float(x[0])+1j*float(x[1]) for x in r] for r in M])
off=0; Uq=[]; Pq=[]; Eq=[]; maxdev=0
for k in range(3):
    n=nb[k]; d=D[k]; t=torch.tensor(th[off:off+sizes[k]]); off+=sizes[k]
    Us=[torch.linalg.matrix_exp(1j*herm(t[2*d*d*x:2*d*d*(x+1)],d)).numpy() for x in range(n)]
    ph=t[2*d*d*n:2*d*d*n+4*d].numpy(); phis=[ph[2*d*o:2*d*o+d]+1j*ph[2*d*o+d:2*d*o+2*d] for o in range(2)]
    phis=[v/np.abs(v).max() for v in phis]
    E=su2(t[-3:]).numpy()
    uq=[cayley_exact(U) for U in Us]; eq=cayley_exact(E)
    assert all(is_unitary(u) for u in uq) and is_unitary(eq)
    maxdev=max([maxdev]+[abs(tofl(a)-b).max() for a,b in zip(uq+[eq],Us+[E])])
    Uq.append(uq); Eq.append(eq); Pq.append([[(q(z.real),q(z.imag)) for z in v] for v in phis])
print('all node unitaries and frames exactly unitary (Gaussian rationals); max |exact - float| = %.2e'%maxdev)
# exact Gram tensors g_k[o][a][b]
G=[]
for k in range(3):
    vec=[[ [sum_c([cm(Uq[k][x][r][c],Pq[k][o][c]) for c in range(D[k])]) for r in range(D[k])] for x in range(nb[k])] for o in range(2)]
    nrm=[sum(a*a+b*b for a,b in Pq[k][o]) for o in range(2)]
    gx=[[[ (lambda s:(s[0]/nrm[o],s[1]/nrm[o]))(sum_c([cm(cc(vec[o][x][r]),vec[o][y][r]) for r in range(D[k])])) for y in range(nb[k])] for x in range(nb[k])] for o in range(2)]
    G.append([[[gx[o][xa[k][a]][xa[k][b]] for b in range(8)] for a in range(8)] for o in range(2)])
def Gio(i,o):
    M=[[O1]*8 for _ in range(8)]
    for a in range(8):
        for b in range(8):
            v=O1
            for k in range(3):
                ak,bk,ik,ok=B3[a][k],B3[b][k],B3[i][k],B3[o][k]
                v=cm(v,cm(cm(cc(Eq[k][ak][ik]),Eq[k][bk][ik]),G[k][ok][a][b]))
            M[a][b]=v
    return M
GG=[[Gio(i,o) for o in range(8)] for i in range(8)]
Gf=np.array([[tofl(GG[i][o]) for o in range(8)] for i in range(8)])
fi=REP[ORB]; Mf=np.einsum('r,rab->ab',Tn[fi,:64],Gf.reshape(64,8,8))+Tn[fi,64]*np.eye(8); w,Ue=np.linalg.eigh(Mf)
psi=Ue[:,0]; psi=psi/psi[np.argmax(abs(psi))]
print('float relative facet value with the exact board: %.10e (orbit %d, facet %d)'%(w[0],ORB,fi))
ps=[(q(x.real),q(x.imag)) for x in psi]; nn=sum(a*a+b*b for a,b in ps)
p=[[None]*8 for _ in range(8)]
for i in range(8):
    for o in range(8):
        s=Z0
        for a in range(8):
            for b in range(8): s=ca(s,cm(cm(cc(ps[a]),GG[i][o][a][b]),ps[b]))
        assert s[1]==0; p[i][o]=s[0]/nn
assert all(x>=0 for r in p for x in r)
for o in range(8): assert sum(p[i][o] for i in range(8))==1
for f in it.product(range(4),repeat=3):
    assert sum(p[i][B3.index(tuple((f[t]>>B3[i][t])&1 for t in range(3)))] for i in range(8))==1
print('p is exactly a valid classical process (positivity, normalisation, 64 deterministic interventions)')
PFi=np.load('../pfs744.npy').astype(int); h=Hi[fi]; v=[int(x) for x in valsI[:,fi]]
X=np.c_[PFi.reshape(744,-1),np.ones(744,int)]
g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]; gq=[Fr(x).limit_denominator(10**4) for x in g]
assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744)); print('facet functional exact on all 744 PFs; max PF value',max(v))
val=sum(gq[8*i+o]*p[i][o] for i in range(8) for o in range(8))+gq[64]
print('EXACT facet value at p: %s ~ %.10e   relative: %.10e'%('(%d digits / %d digits)'%(len(str(val.numerator)),len(str(val.denominator))),float(val),float(val/max(v))))
print('CERTIFIED: facet %d (orbit %d) is violated.'%(fi,ORB) if val<0 else 'NOT certified (value >= 0)')
json.dump({'W':W,'orb':ORB,'facet':int(fi),'DEN':DEN,'value_float':float(val),'rel':float(val/max(v)),'violated':bool(val<0)},open(pf.replace('.npy','_cert.json'),'w'))
