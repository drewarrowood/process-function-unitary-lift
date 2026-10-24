"""Round 15, H.22.2: the generalised Lugano board L_{U_A,U_B,U_C} is a fleshing-out of VOKB's Lugano routed graph [PROVED, CITED step].
In VOKB's Lugano circuit (Fig. 30, as re-encoded in rg_h12.py (c)) node k applies a controlled-X from the index l to the unindexed
past qubit p_k.  Replacing it by a controlled-U_k (any qubit unitary) changes no route.  The consistent index assignment r for
each agent output a does not involve the gates at all, so the composite is L_{U_A,U_B,U_C} for every choice of gates.
We check this for X,X,X (Lugano), X,sqrtX,X (H.12) and 200 Haar triples, and for the time reverse (graph reversed, H.15.7e.3)."""
import itertools as it, numpy as np
B3=list(it.product((0,1),repeat=3)); ix=B3.index
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b); k3=lambda a,b,c:np.kron(np.kron(a,b),c)
C={(i,j,k,(1-j)*k,(1-k)*i,(1-i)*j) for i,j,k in B3}; C={c for c in C if c[0]*c[3]==0 and c[1]*c[4]==0 and c[2]*c[5]==0}
assign={}; ok=True; recs={}
for a in B3:
    sols=[]
    for r in B3:
        votes=[a[k] if r[k]==0 else 0 for k in range(3)]
        if tuple(votes)+r in C: sols.append((r,(tuple(votes),tuple((r[k],a[k] if r[k] else None) for k in range(3)))))
    ok&=len(sols)==1; r,rec=sols[0]; assign[a]=r; recs.setdefault(rec,set()).add(a)
inj=len(recs)==8 and all(len(v)==1 for v in recs.values())
print('gate-independent: unique consistent assignment per agent output:',ok,'; F record determines a:',inj,
      '; assignment r(a) == lug(a) for all a:',all(assign[a]==lug(*a) for a in B3))
def comp(U):
    M=np.zeros((64,64),complex)
    for a in B3:
        g=k3(*[np.linalg.matrix_power(U[k],assign[a][k]) for k in range(3)])
        for s in range(8):
            for i in range(8): M[8*i+ix(a),8*ix(a)+s]+=g[i,s]
    return M
def L(U):
    M=np.zeros((64,64),complex)
    for o in range(8):
        g=k3(*[np.linalg.matrix_power(U[k],lug(*B3[o])[k]) for k in range(3)])
        for s in range(8):
            for i in range(8): M[8*i+o,8*o+s]=g[i,s]
    return M
X=np.array([[0,1],[1,0]],complex); G=np.array([[1+1j,1-1j],[1-1j,1+1j]])/2
rng=np.random.default_rng(0)
def haar():
    q,r=np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))); return q*(np.diag(r)/abs(np.diag(r)))
tests=[[X,X,X],[X,G,X]]+[[haar() for _ in range(3)] for _ in range(200)]
print('composite == L_{U_A,U_B,U_C} for Lugano, sqrtX-Lugano and 200 Haar triples: max dev %.1e'%max(abs(comp(U)-L(U)).max() for U in tests))
def loop(V,Ms):   # closed loop P->F with agent unitaries Ms (AI->AO), V rows (AI,F) cols (AO,P)
    W=V.reshape(8,8,8,8); M=k3(*Ms); Tm=np.zeros((8,8),complex)
    # sum over consistent loops: F,s amplitude = sum_{i,o} W[i,F,o,s] M[o,i]
    Tm=np.einsum('ifos,oi->fs',W,M); return abs(Tm.conj().T@Tm-np.eye(8)).max()
dev=max(loop(Vv,[haar() for _ in range(3)]) for U in tests[:50] for Vv in (L(U),L(U).T) for _ in range(5))
print('closed loop with random local unitaries is unitary (L and L^T, 50 triples x 5 draws): max dev %.1e'%dev)
