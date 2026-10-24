"""Round 14, item 2: a tighter relaxation for min y_A.P over instruments on H.12 (H.15.9(C)).
'Lifted-A' relaxation: party A's two POVMs act on two copies A, A' of its qubit.  For products,
  Zh[cA0,cA1,xB,xC,cB,cC] = E^A_{cA0|0} (x) E^A_{cA1|1} (x) E^B_{cB|xB} (x) E^C_{cC|xC}   on (A,A',B,C), 16x16,
satisfies: Zh >= 0;  sum over all outcomes = 1_16 for each (xB,xC);  sum_{cA1} Zh = M (x) 1_{A'};  sum_{cA0} Zh = 1_A (x) M';
NS for B and C (sum over c_k = 1_k (x) R, R independent of x_k);  optional PPT on each single qubit.
The x_A=0 correlations are Tr_{A'} sum_{cA1} Zh / 2 and the x_A=1 ones Tr_A sum_{cA0} Zh / 2 (A' in the role of A).
So min y_A.P over this set is a lower bound for every product of POVMs, hence (H.15.7d reduction) for every instrument.
Every feasible point projects to a point of the NS relaxation of h12_bound.py, so the bound is at least as tight.  [NUMERICAL; SCS]"""
import numpy as np, itertools as it, cvxpy as cp, sys, re, time
sys.path.insert(0,'.')
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2
psi=np.array([U[o]@ph for o in range(8)])
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),float).reshape(8,8)
ppt='ppt' in sys.argv; eps=float(sys.argv[1]) if len(sys.argv)>1 and sys.argv[1][0].isdigit() else 1e-5
I2=np.eye(2); Pl=[I2,np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1])]
def op4(ms):  # ms: dict qubit->2x2, order (A,A',B,C)
    M=np.array([[1.]])
    for q in range(4): M=np.kron(M,ms.get(q,I2))
    return M
def twirl(S,q): return sum(op4({q:P})@S@op4({q:P}).conj().T for P in Pl)/4
def emb(W8,first):   # W on (A,B,C) -> on (A,A',B,C), A-factor on qubit `first` (0 or 1), identity on the other
    W=W8.reshape(2,2,2,2,2,2)   # a b c, a' b' c'
    E=np.einsum('abcdef,gh->agbcdhef',W,I2) if first==0 else np.einsum('abcdef,gh->gabchdef',W,I2)
    return E.reshape(16,16)
pc=lambda c:(c>>1,c&1)   # party outcome c in 0..3 -> (a,o)
t0=time.time()
Z={k:cp.Variable((16,16),hermitian=True) for k in it.product(range(4),range(4),(0,1),(0,1),range(4),range(4))}
cons=[v>>0 for v in Z.values()]
for xb,xc in it.product((0,1),repeat=2):
    cons.append(sum(Z[cA0,cA1,xb,xc,cB,cC] for cA0,cA1,cB,cC in it.product(range(4),repeat=4))==np.eye(16))
for xb,xc,cB,cC in it.product((0,1),(0,1),range(4),range(4)):
    for c in range(4):
        S=sum(Z[c,c1,xb,xc,cB,cC] for c1 in range(4)); cons.append(S==twirl(S,1))
        S=sum(Z[c0,c,xb,xc,cB,cC] for c0 in range(4)); cons.append(S==twirl(S,0))
for cA0,cA1 in it.product(range(4),repeat=2):
    for xc,cC in it.product((0,1),range(4)):
        S=[sum(Z[cA0,cA1,xb,xc,cB,cC] for cB in range(4)) for xb in (0,1)]
        cons+=[S[1]==S[0],S[0]==twirl(S[0],2)]
    for xb,cB in it.product((0,1),range(4)):
        S=[sum(Z[cA0,cA1,xb,xc,cB,cC] for cC in range(4)) for xc in (0,1)]
        cons+=[S[1]==S[0],S[0]==twirl(S[0],3)]
if ppt:
    for v in Z.values():
        for q in range(4): cons.append(cp.partial_transpose(v,[2,2,2,2],q)>>0)
W={o:np.outer(psi[o],psi[o].conj()) for o in range(8)}
obj=0
for (cA0,cA1,xb,xc,cB,cC),v in Z.items():
    (aB,oB),(aC,oC)=pc(cB),pc(cC); Cm=np.zeros((16,16),complex)
    for xa,cA,first in ((0,cA0,0),(1,cA1,1)):
        aA,oA=pc(cA); w=y[B3.index((xa,xb,xc)),B3.index((aA,aB,aC))]
        if w: Cm+=w*emb(W[B3.index((oA,oB,oC))],first)/2
    if np.abs(Cm).max()>0: obj=obj+cp.real(cp.trace(Cm@v))
pr=cp.Problem(cp.Minimize(obj),cons)
print('built',len(Z),'vars',len(cons),'constraints',f'{time.time()-t0:.0f}s',flush=True)
pr.solve(solver='SCS',eps=eps,max_iters=200000,verbose=True)
print(f'LIFT-A {"NS+PPT" if ppt else "NS"} y_A: status {pr.status}, value {pr.value:.6f}, time {time.time()-t0:.0f}s',flush=True)
import pickle; pickle.dump({k:v.value for k,v in Z.items()},open(f'/tmp/r14/lift_{"ppt" if ppt else "ns"}.pkl','wb'))
