# Exact rational certificate that E_ex1 is not purifiable (AFNB Thm 4), using python-flint.
import numpy as np, itertools as it, flint, sys
from fractions import Fraction
sys.argv=['x']
import importlib.util
spec=importlib.util.spec_from_file_location('f2','fast2.py'); f2=importlib.util.module_from_spec(spec); spec.loader.exec_module(f2)
B3=f2.B3
def P(w):
    M=np.zeros((8,8))
    for a in B3: M[B3.index(w(a)),B3.index(a)]=1
    return M
C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
E=(P(C)+P(Cb))/2; d=f2.diagW(E); supp=list(np.nonzero(d>0)[0]); r=len(supp)
Q=lambda x: flint.fmpq(Fraction(float(x)).limit_denominator(1<<20).numerator, Fraction(float(x)).limit_denominator(1<<20).denominator)
assert np.allclose(f2.L*64, np.round(f2.L*64))
emb=np.zeros((4096,64*r))
for k,p in enumerate(supp):
    for row in range(64): emb[row*64+p,row*r+k]=1
A=(f2.L@emb)*64; A=np.round(A).astype(int)
rows=[i for i in range(4096) if A[i].any()]
M=flint.fmpz_mat([[int(v) for v in A[i]] for i in rows])
N=M.nullspace()[0]   # columns basis (fmpz_mat), may include zero columns
k=M.nullspace()[1]; print('exact dim V_W',k)
Nb=[[N[i,j] for i in range(N.nrows())] for j in range(k)]
Nb=np.array([[int(v) for v in col] for col in Nb]).T   # (64r, k) integer
Xs=[(emb@Nb[:,a]).reshape(64,64) for a in range(k)]
Lam=np.zeros(64); Lam[supp]=2  # 1/E = 2
# constraint vectors T[a,b] = 64*L(X_a Lam X_b^T)  (all real integers)
T=np.array([[np.round(64*(f2.L@(Xs[a]@np.diag(Lam)@Xs[b].T).ravel())).astype(np.int64) for b in range(k)] for a in range(k)])
# a form is any functional phi on 4096-space: B_phi(a,b)=phi.T[a,b]. pick phi = rows of identity, search for a symmetric form with small isotropic bound
def inertia(S):
    # exact inertia of symmetric rational matrix via congruence (symmetric Gaussian elimination)
    S=flint.fmpq_mat(S); n=S.nrows(); pos=neg=zero=0
    S=[[S[i,j] for j in range(n)] for i in range(n)]
    idx=list(range(n))
    while idx:
        piv=next((i for i in idx if S[i][i]!=0),None)
        if piv is None:
            pair=next(((i,j) for i in idx for j in idx if i<j and S[i][j]!=0),None)
            if pair is None: zero+=len(idx); break
            i,j=pair
            for t in range(n): S[i][t]+=S[j][t]
            for t in range(n): S[t][i]+=S[t][j]
            continue
        p=S[piv][piv]; pos+= p>0; neg+= p<0
        for i in idx:
            if i!=piv and S[i][piv]!=0:
                f=S[i][piv]/p
                for t in range(n): S[i][t]-=f*S[piv][t]
                for t in range(n): S[t][i]-=f*S[t][piv]
        idx.remove(piv)
    return pos,neg,zero
best=None
used=np.nonzero(np.abs(T).sum(axis=(0,1)))[0]
for c in used:
    Bm=T[:,:,c]; S=(Bm+Bm.T)
    if not S.any(): continue
    p,n_,z=inertia([[int(v) for v in row] for row in S])
    b=z+min(p,n_)
    if best is None or b<best[0]: best=(b,int(c),p,n_,z)
print('rank',r,'best exact isotropic bound',best)

rng=np.random.default_rng(0); Tu=T[:,:,used].astype(float)
found=None
for trial in range(4000):
    phi=rng.integers(-3,4,size=len(used))*(rng.random(len(used))<0.05)
    S=np.einsum('abc,c->ab',Tu,phi); S=S+S.T
    if not S.any(): continue
    e=np.linalg.eigvalsh(S); z=np.sum(abs(e)<1e-6); b=z+min(np.sum(e>1e-6),np.sum(e<-1e-6))
    if b<r:
        p,n_,zz=inertia([[int(v) for v in row] for row in np.round(S).astype(np.int64)])
        if zz+min(p,n_)<r: found=(trial,int(zz+min(p,n_)),p,n_,zz); break
print('exact certificate (trial, bound, pos, neg, zero):',found)
if found: np.save('cert_phi.npy',phi); np.save('cert_used.npy',used)
