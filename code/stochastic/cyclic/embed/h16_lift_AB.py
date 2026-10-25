"""Round 16, item 3: intersection of the lift-A and lift-B relaxations of H.21.8 / H.22.1 (primal, SCS).
Two variable families: Z^A on (A,A',B,C) and Z^B on (B,B',A,C), each with all constraints of h12_lift.py (relabelled as in LIFTP=1),
linked by equality of the induced NS families: for every setting triple x and outcome triple c the 8x8 operator on (A,B,C)
read from Z^A equals the one read from Z^B.  Products of POVMs are feasible in both with the same NS family, so the minimum of
y_A.P over the intersection is again a lower bound over all instruments, at least as tight as each lift.  [NUMERICAL; SCS]
Optional third family (argument 'C'): also lift C."""
import numpy as np, itertools as it, cvxpy as cp, sys, re, time
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2
psi=np.array([U[o]@ph for o in range(8)])
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),float).reshape(8,8)
eps=float(sys.argv[1]) if len(sys.argv)>1 else 1e-5
LIFTS=[0,1]+([2] if 'C' in sys.argv else [])
I2=np.eye(2); Pl=[I2,np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1])]
def opn(ms,n):
    M=np.array([[1.]])
    for q in range(n): M=np.kron(M,ms.get(q,I2))
    return M
def twirl(S,q): return sum(opn({q:P},4)@S@opn({q:P},4).conj().T for P in Pl)/4
def qperm(order):   # permutation matrix P with P (x_{order[0]} x x_{order[1]} x x_{order[2]}) = (x_0 x x_1 x x_2) on 3 qubits
    P=np.zeros((8,8))
    for b in B3:
        src=tuple(b[order[i]] for i in range(3)); P[B3.index(b),B3.index(src)]=1
    return P
def emb(W8,first):
    W=W8.reshape(2,2,2,2,2,2)
    E=np.einsum('abcdef,gh->agbcdhef',W,I2) if first==0 else np.einsum('abcdef,gh->gabchdef',W,I2)
    return E.reshape(16,16)
pc=lambda c:(c>>1,c&1)
W={o:np.outer(psi[o],psi[o].conj()) for o in range(8)}
t0=time.time(); cons=[]; NSF={}; obj=None
for L in LIFTS:
    order=[L]+[j for j in range(3) if j!=L]; M_,N_=order[1],order[2]
    P=qperm(order)          # maps (L,M,N)-ordered vectors to (A,B,C)-ordered
    Z={k:cp.Variable((16,16),hermitian=True) for k in it.product(range(4),range(4),(0,1),(0,1),range(4),range(4))}
    cons+=[v>>0 for v in Z.values()]
    for xm,xn in it.product((0,1),repeat=2):
        cons.append(sum(Z[a,b,xm,xn,c,d] for a,b,c,d in it.product(range(4),repeat=4))==np.eye(16))
    for xm,xn,cm,cn in it.product((0,1),(0,1),range(4),range(4)):
        for c in range(4):
            S=sum(Z[c,c1,xm,xn,cm,cn] for c1 in range(4)); cons.append(S==twirl(S,1))
            S=sum(Z[c0,c,xm,xn,cm,cn] for c0 in range(4)); cons.append(S==twirl(S,0))
    for a,b in it.product(range(4),repeat=2):
        for xn,cn in it.product((0,1),range(4)):
            S=[sum(Z[a,b,xm,xn,cm,cn] for cm in range(4)) for xm in (0,1)]; cons+=[S[1]==S[0],S[0]==twirl(S[0],2)]
        for xm,cm in it.product((0,1),range(4)):
            S=[sum(Z[a,b,xm,xn,cm,cn] for cn in range(4)) for xn in (0,1)]; cons+=[S[1]==S[0],S[0]==twirl(S[0],3)]
    # induced NS family in original (A,B,C) order: F[x,c] (8x8)
    F={}
    for xl,xm,xn in it.product((0,1),repeat=3):
        for cl,cm,cn in it.product(range(4),repeat=3):
            if xl==0: S=sum(Z[cl,c1,xm,xn,cm,cn] for c1 in range(4)); R=cp.partial_trace(S,[2,2,2,2],1)/2
            else:     S=sum(Z[c0,cl,xm,xn,cm,cn] for c0 in range(4)); R=cp.partial_trace(S,[2,2,2,2],0)/2
            x=[0,0,0]; c=[0,0,0]; x[L],x[M_],x[N_]=xl,xm,xn; c[L],c[M_],c[N_]=cl,cm,cn
            F[tuple(x),tuple(c)]=P@R@P.T
    NSF[L]=F
    if obj is None:   # objective from the first family: sum_x,c y[x,a] Tr[F[x,c] W_o] (same as h12_lift's objective)
        obj=0
        for (x,c),R in F.items():
            a=tuple(pc(ci)[0] for ci in c); o=tuple(pc(ci)[1] for ci in c); w=y[B3.index(x),B3.index(a)]
            if w: obj=obj+w*cp.real(cp.trace(W[B3.index(o)]@R))
    print('family',L,'built',f'{time.time()-t0:.0f}s',flush=True)
for L in LIFTS[1:]:
    for k in NSF[0]: cons.append(NSF[0][k]==NSF[L][k])
pr=cp.Problem(cp.Minimize(obj),cons)
print('built',len(cons),'constraints',f'{time.time()-t0:.0f}s',flush=True)
pr.solve(solver='SCS',eps=eps,max_iters=200000,verbose=True)
print(f'LIFT-{"".join("ABC"[l] for l in LIFTS)} intersection y_A: status {pr.status}, value {pr.value:.6f}, time {time.time()-t0:.0f}s',flush=True)
