"""Round 16 (H.23.3) sanity check of the linking identity used by h16_liftAB_scs.py / h16_liftAB_verify.py:
for product strategies Z^L_v = M^L_{0,c0} (x) M^L_{1,c1} (x) M^M_{xM,cM} (x) M^N_{xN,cN} (random 4-outcome qubit POVMs M^k_{x,c}),
sum_v Tr[K^A_v(Lam) Z^A_v] = sum_v Tr[K^B_v(Lam) Z^B_v] for random Hermitian Lam, and both equal sum_{x,c} Tr[Lam_{x,c} M^A(x) M^B (x) M^C].  [NUMERICAL]"""
import numpy as np, itertools as it
rng=np.random.default_rng(7); B3=list(it.product((0,1),repeat=3)); I2=np.eye(2)
def povm():
    G=[rng.normal(size=(2,2))+1j*rng.normal(size=(2,2)) for _ in range(4)]; P=[g@g.conj().T for g in G]; S=sum(P)
    w,U=np.linalg.eigh(S); Si=U@np.diag(w**-.5)@U.conj().T; return [Si@p@Si for p in P]
M={(k,x):povm() for k in range(3) for x in (0,1)}
def embQ(first):
    Q=np.zeros((16,16))
    for a in range(8):
        for g in (0,1):
            t=B3[a]; dst=(t[0],g,t[1],t[2]) if first==0 else (g,t[0],t[1],t[2]); Q[int(''.join(map(str,dst)),2),a*2+g]=1
    return Q
QE=[embQ(0),embQ(1)]
Lam={}
for k in it.product(range(8),range(64)):
    X=rng.normal(size=(8,8))+1j*rng.normal(size=(8,8)); Lam[k]=X+X.conj().T
def side(L):
    perm=[L]+[j for j in range(3) if j!=L]; orig=lambda t:tuple(t[perm.index(j)] for j in range(3))
    qidx=np.array([B3.index(orig(B3[a])) for a in range(8)]); m,n=perm[1],perm[2]; tot=0
    for c0,c1,xm,xn,cm,cn in it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)):
        Z=np.kron(np.kron(np.kron(M[L,0][c0],M[L,1][c1]),M[m,xm][cm]),M[n,xn][cn])
        for xl,cl in ((0,c0),(1,c1)):
            xo=orig((xl,xm,xn)); co=orig((cl,cm,cn)); X=Lam[B3.index(xo),16*co[0]+4*co[1]+co[2]][np.ix_(qidx,qidx)]
            tot+=np.trace(QE[xl]@np.kron(X,I2)@QE[xl].T@Z)/2
    return tot
ref=sum(np.trace(Lam[B3.index(x),16*c[0]+4*c[1]+c[2]]@np.kron(np.kron(M[0,x[0]][c[0]],M[1,x[1]][c[1]]),M[2,x[2]][c[2]]))
        for x in B3 for c in it.product(range(4),repeat=3))
a,b=side(0),side(1)
print(f'family A {a.real:.10f}  family B {b.real:.10f}  direct {ref.real:.10f}  max diff {max(abs(a-b),abs(a-ref)):.2e}')
