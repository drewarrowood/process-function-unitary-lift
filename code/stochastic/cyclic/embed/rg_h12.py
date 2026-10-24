"""H.21.2 (Round 14): H.12 is the Hadamard-rotated TIME REVERSE of a sqrt(X)-Lugano process, hence has a valid routed graph [exact].
Phase form (tds_h12.py): D: |z>_P|o>_AO -> i^{pre(z)} (-1)^{oA (zB or zC)} i^{oB zA zC} (-1)^{oC zB (1-zA)} |z>_AI|o>_F.
A Hadamard on each agent output and on F turns the oA, oC phases into X flips and the oB phase S^{zA zC} into (h S h)^{zA zC},
with h S h = sqrt(X) = (1/2)[[1+i,1-i],[1-i,1+i]].  Relabelling zC -> 1-zC gives the flip conditions
(1 + lug_A(z), lug_B(z), lug_C(z)), lug(a,b,c) = ((1-b)c,(1-c)a,(1-a)b).  Define for a qubit unitary G
   L_G: |s>_P|o>_AO -> (X^{lug_A(o)} (x) G^{lug_B(o)} (x) X^{lug_C(o)}) |s>_AI |o>_F      (L_X = Lugano purification L).
Claim (exact, Gaussian-integer arithmetic):  V_H12 = (Hd X_C)_AI (Hd X_A)_F . L_G^T . (Hd)_AO (X_C Pre Hd)_P,  G = sqrt(X) (G^T = G),
Pre = diag(i^{pre(z)}).  Routed graph: VOKB's Lugano graph (Fig. 27) may be fleshed out with ANY operations following its routes
(VOKB Sec. 4.3, 'a larger family of processes'); in their circuit the past qubit p_B and Bob's input are unindexed, so replacing
node B's CNOT (l -> p_B) by a controlled-G leaves every route unchanged.  We check that this fleshing composes to L_G exactly
(unique consistent index assignment per agent output, as in rg_lugano_flesh.py), then reverse the graph as in H.15.7e.3."""
import itertools as it, numpy as np, sys, io, contextlib
sys.argv=[sys.argv[0]]
with contextlib.redirect_stdout(io.StringIO()):
    from rg_check import analyse
    from rg_lugano import lugano_graph
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1; ix=B3.index
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
H=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)],complex)        # sqrt(8) Hd, integer
ipow=lambda k:[1,1j,-1,-1j][k%4]
V8=np.zeros((64,64),complex)                                                     # 8 V_H12, Gaussian integers
for o in range(8):
    U=H@np.diag([ipow(MT[o][z]) for z in range(8)])@H
    for i in range(8):
        for s in range(8): V8[8*i+o,8*o+s]=U[i,s]
I2=np.eye(2); X=np.array([[0,1],[1,0]],complex); G2=np.array([[1+1j,1-1j],[1-1j,1+1j]])   # G2 = 2 sqrt(X)
k3=lambda a,b,c:np.kron(np.kron(a,b),c)
print('(a) (G2/2)^2 = X:',np.array_equal(G2@G2,4*X),'; G = h S h:',np.allclose(G2/2,np.array([[1,1],[1,-1]])@np.diag([1,1j])@np.array([[1,1],[1,-1]])/2))
def LGT2():    # 2 L_G^T, layout rows 8*agent_in + future, cols 8*agent_out + past ; (p,q) -> (p, gates(p) q)
    M=np.zeros((64,64),complex)
    for p in range(8):
        a,b,c=lug(*B3[p]); g=k3(np.linalg.matrix_power(X,a),G2 if b else 2*I2,np.linalg.matrix_power(X,c))
        for q in range(8):
            for f in range(8): M[8*p+f,8*q+p]+=g[f,q]
    return M
Xc=k3(I2,I2,X); XA=k3(X,I2,I2)
Pre=np.diag([ipow(3*z[2]+2*z[0]+z[1]*z[2]+3*z[0]*z[2]+z[0]*z[1]+2*z[0]*z[1]*z[2]) for z in B3])
R=np.kron(H@Xc,H@XA)@LGT2()@np.kron(H,Xc@Pre@H)                                   # = 128 RHS
print('(b) exact: 128 (Hd X_C)(Hd X_A) L_G^T (Hd)(X_C Pre Hd) == 16 (8 V_H12):',np.array_equal(R,16*V8),
      ' (all entries Gaussian integers:',np.array_equal(R,np.round(R.real)+1j*np.round(R.imag)),')')
# (c) fleshing-out of VOKB Fig. 30 with node B's CNOT replaced by controlled-G, composed by consistent index assignments
C={(i,j,k,(1-j)*k,(1-k)*i,(1-i)*j) for i,j,k in B3}; C={c for c in C if c[0]*c[3]==0 and c[1]*c[4]==0 and c[2]*c[5]==0}
gates=[X,G2/2,X]; comp=np.zeros((64,64),complex); ok=True; recs={}
for a in B3:
    sols=[]
    for r in B3:
        votes=[a[k] if r[k]==0 else 0 for k in range(3)]
        if tuple(votes)+r in C: sols.append((r,(tuple(votes),tuple((r[k],a[k] if r[k] else None) for k in range(3)))))
    if len(sols)!=1: ok=False
    r,rec=sols[0]; recs.setdefault(rec,set()).add(a)
    g=k3(*[np.linalg.matrix_power(gates[k],r[k]) for k in range(3)])   # node k: controlled-gate (index r_k -> p_k)
    for s in range(8):
        for i in range(8): comp[8*i+ix(a),8*ix(a)+s]+=g[i,s]            # F record determines a: relabel record -> |a>
inj=len(recs)==8 and all(len(v)==1 for v in recs.values())
LG=np.zeros((64,64),complex)
for o in range(8):
    a,b,c=lug(*B3[o]); g=k3(np.linalg.matrix_power(X,a),np.linalg.matrix_power(G2/2,b),np.linalg.matrix_power(X,c))
    for s in range(8):
        for i in range(8): LG[8*i+o,8*o+s]=g[i,s]
print('(c) unique consistent assignment per agent output:',ok,'; F record determines a:',inj,'; composite == L_G exactly:',np.array_equal(comp,LG))
print('    L_G^T == transpose of L_G:',np.array_equal(2*LG.T,LGT2()))
ar,Rt,_=lugano_graph(); arR={k:(d,s,x) for k,(s,d,x) in ar.items()}; RR={N:{(o,i) for i,o in rel} for N,rel in Rt.items()}
analyse(arR,RR,'time-reversed VOKB Fig. 27 = routed graph for L_G^T, hence for H.12 after local unitaries')
