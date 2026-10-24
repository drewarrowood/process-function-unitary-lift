"""F.5.9 check [numerical sanity check of a PROVED statement]: finitely controlled non-causal w.
Lugano function on cells (sign bit of each output), lifted to the grid Z_N (N even, cells = halves),
translations by N/2 * Lugano bit. Local unitaries: DFT on Z_N (x) random ancilla unitary, plus random dense unitaries.
Checks: (1) w is a process function on Z_N^3 (exactly one fixed point for all local maps, sampled + exhaustive on cells);
(2) the finite-sum operator M = sum_c (x)_k P_{c_k} V_k S_{w_k(c)} equals the F.2 matrix; (3) M is unitary;
(4) operator column identity sum_c (x)_k F_k(w_k(c),c_k) = 1 for random non-commuting PVM families."""
import numpy as np, itertools as it
rng=np.random.default_rng(7)
def lug(c):  # Baumeler-Wolf Lugano on bits
    a,b,cc=c; return ((1-b)*cc, (1-cc)*a, (1-a)*b)
# (1a) Lugano is a process function on bits (exhaustive over local functions)
ok=True
for fs in it.product(it.product((0,1),repeat=2),repeat=3):
    n=sum(1 for c in it.product((0,1),repeat=3) if all(fs[k][lug(c)[k]]==c[k] for k in range(3)))
    ok&=(n==1)
print('(1a) Lugano on bits: unique fixed point for all 64 local function triples:',ok)
N=4; H=N//2; cell=lambda x: int(x>=H)
def w(o): return tuple(H*v for v in lug(tuple(cell(x) for x in o)))
# (1b) lifted w on Z_N^3: unique fixed point for random local maps (exhaustive on outputs)
ok=True
for t in range(3000):
    f=[rng.integers(0,N,N) for _ in range(3)]
    n=sum(1 for o in it.product(range(N),repeat=3) if all(f[k][w(o)[k]]==o[k] for k in range(3)))
    ok&=(n==1)
print('(1b) lifted w on Z_%d^3: unique fixed point, 3000 random local map triples:'%N,ok)
d=2  # ancilla dim per party
F=np.exp(2j*np.pi*np.outer(range(N),range(N))/N)/np.sqrt(N)
def haar(n):
    z=(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
for trial,kind in enumerate(['DFT x haar','haar']):
    V=[np.kron(F,haar(d)) if kind=='DFT x haar' else haar(N*d) for _ in range(3)]
    D=N*d
    def S(a):  # (S_a psi)(i) = psi(i - a) on Z_N, identity on ancilla
        P=np.zeros((N,N)); 
        for i in range(N): P[i,(i-a)%N]=1
        return np.kron(P,np.eye(d))
    def Pc(c): return np.kron(np.diag([1.0 if cell(x)==c else 0 for x in range(N)]),np.eye(d))
    M=np.zeros((D**3,D**3),complex)
    for c in it.product((0,1),repeat=3):
        a=[H*v for v in lug(c)]
        ops=[Pc(c[k])@V[k]@S(a[k]) for k in range(3)]
        M+=np.kron(np.kron(ops[0],ops[1]),ops[2])
    # F.2 matrix: <o,y|M|e,x> = prod_k <o_k,y_k|V_k|w_k(o)+e_k, x_k>
    M2=np.zeros_like(M); idx=lambda o,y: o*d+y
    for o in it.product(range(N),repeat=3):
        wo=w(o)
        for y in it.product(range(d),repeat=3):
            r=np.ravel_multi_index([idx(o[k],y[k]) for k in range(3)],(D,D,D))
            row=1
            for k in range(3):
                vk=np.zeros(D,complex)
                for e in range(N):
                    vk[e*d:(e+1)*d]=V[k][idx(o[k],y[k]),((wo[k]+e)%N)*d:((wo[k]+e)%N+1)*d]
                row=np.kron(row,vk)
            M2[r]=row
    print('(2,3) %s: |M - F.2 matrix| = %.2e, |M M^+ - 1| = %.2e, |M^+ M - 1| = %.2e'%(kind,abs(M-M2).max(),abs(M@M.conj().T-np.eye(D**3)).max(),abs(M.conj().T@M-np.eye(D**3)).max()))
# (4) operator column identity with random PVMs on C^m, families indexed by translation value a in {0,1} (Lugano bit)
m=3
for t in range(3):
    Fk=[]
    for k in range(3):
        fam={}
        for a in (0,1):
            U=haar(m); r=rng.integers(1,m); P0=U[:,:r]@U[:,:r].conj().T
            fam[a]=(P0,np.eye(m)-P0)
        Fk.append(fam)
    T=sum(np.kron(np.kron(Fk[0][lug(c)[0]][c[0]],Fk[1][lug(c)[1]][c[1]]),Fk[2][lug(c)[2]][c[2]]) for c in it.product((0,1),repeat=3))
    comm=max(abs(Fk[k][0][0]@Fk[k][1][0]-Fk[k][1][0]@Fk[k][0][0]).max() for k in range(3))
    print('(4) trial %d: max commutator %.2f, |sum_c (x) F - 1| = %.2e'%(t,comm,abs(T-np.eye(m**3)).max()))
# (5) the decomposition F(a,c) = sum_{f: f(a)=c} G_f, G_f = r^(1-m) sum_a F(a,f(a)) - (m-1) r^(-m) 1, sum_f G_f = 1
mA,r=3,3
Fam={a:[None]*r for a in range(mA)}
for a in range(mA):
    U=haar(4); Fam[a]=[U[:,[0]]@U[:,[0]].conj().T, U[:,[1]]@U[:,[1]].conj().T, U[:,2:]@U[:,2:].conj().T]
fs=list(it.product(range(r),repeat=mA))
G={f:r**(1-mA)*sum(Fam[a][f[a]] for a in range(mA))-(mA-1)*r**(-mA)*np.eye(4) for f in fs}
e1=max(abs(sum(G[f] for f in fs if f[a]==c)-Fam[a][c]).max() for a in range(mA) for c in range(r))
e2=abs(sum(G.values())-np.eye(4)).max()
print('(5) decomposition (m=3 inputs, r=3 outcomes, dim 4): max |F - sum G| = %.2e, |sum_f G_f - 1| = %.2e'%(e1,e2))
