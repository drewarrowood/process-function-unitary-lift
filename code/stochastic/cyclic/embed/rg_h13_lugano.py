"""H.15.7e(A): H.13.2 is the Hadamard-rotated TIME REVERSE of the Lugano purification (up to local Pauli X flips) [exact].
f(z) = (z_B z_C, z_A(1+z_C), z_A OR z_B) (rg_h13.py) is a process function, and f(o) = lug(o + fo) + fi with fo=(0,1,0), fi=(0,0,1),
lug(a,b,c) = ((1-b)c, (1-c)a, (1-a)b).  The Lugano purification L: |s>_P|o>_AO -> |s + lug(o)>_AI |o>_F is a permutation;
its time reverse L^T has past F, agent inputs AO, agent outputs AI, future P.  Claim (checked exactly, integer matrices):
   V_13.2 = (Hd X^fo)_AI (Hd X^fi)_F . L^T . (X^fo Hd)_P (Hd)_AO   (as maps P x AO -> AI x F, wires relabelled as in L^T).
Then: the reverse of VOKB's valid Lugano graph (all arrows reversed, routes transposed) is valid (checked with rg_check), and
the local unitaries on agent wires are absorbed into the agent nodes, those on P/F into the global past/future."""
import itertools as it, json, numpy as np, sys, io, contextlib
sys.argv=[sys.argv[0]]
with contextlib.redirect_stdout(io.StringIO()):
    from rg_check import analyse
    from rg_lugano import lugano_graph
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1; ix=B3.index
f=lambda z:(z[1]*z[2], z[0]*(1-z[2]), z[0]|z[1]); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b); xo=lambda u,v:tuple(p^q for p,q in zip(u,v))
fo,fi=(0,1,0),(0,0,1)
H=lambda: np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])
def ok_pf(F):
    return all(len([i for i in B3 if F(tuple(h[k][i[k]] for k in range(3)))==i])==1 for h in it.product(list(it.product((0,1),repeat=2)),repeat=3))
print('f is a process function:',ok_pf(f),'; f(o) = lug(o+fo)+fi for all o:',all(f(o)==xo(lug(*xo(o,fo)),fi) for o in B3))
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
V=np.zeros((64,64),int)                      # rows (i_AI, o_F), cols (o_AO, s_P); entries 8*U_o[i,s]
for o in range(8):
    U8=H()@np.diag([(-1)**(m[o][z]//2) for z in range(8)])@H()
    for i in range(8):
        for s in range(8): V[8*i+o,8*o+s]=U8[i,s]
# L^T as a map (past'=F-label p, agent-out'=AI-label q) -> (agent-in'=AO-label, future'=P-label):  (p,q) -> (p, q + lug(p))
LT=np.zeros((64,64),int)
for p in B3:
    for q in B3: LT[8*ix(p)+ix(xo(q,lug(*p))),8*ix(q)+ix(p)]=1    # rows (agent-in, future), cols (agent-out, past)
Xm=lambda t:np.array([[int(ix(xo(B3[c],t))==r) for c in range(8)] for r in range(8)])
AI=H()@Xm(fo); Fu=H()@Xm(fi); Pa=Xm(fo)@H(); AO=H()
R=np.kron(AI,Fu)@LT@np.kron(AO,Pa)            # scale 8^2 = 64 ; V has scale 8 -> compare 8V
print('exact: V_13.2 = (Hd X^fo)_AI (Hd X^fi)_F L^T (Hd)_AO (X^fo Hd)_P :',np.array_equal(R,8*V))
# reversed VOKB graph: every arrow reversed, every route transposed (global past/future swap roles)
ar,Rt,C=lugano_graph()
arR={a:(d,s,ixs) for a,(s,d,ixs) in ar.items()}
RR={N:{(o,i) for i,o in rel} for N,rel in Rt.items()}
analyse(arR,RR,'time-reversed VOKB Fig. 27 (graph for L^T, hence for H.13.2 after local unitaries)')
