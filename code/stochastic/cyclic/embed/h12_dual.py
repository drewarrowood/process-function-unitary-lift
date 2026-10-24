"""H.15.9(C'): dual of the H.12 relaxation of h12_bound.py (NS [+PPT]), solved numerically and saved for exact verification
(h12_dual_verify.py).  Dual: maximise sum_x Tr Lam_x over Hermitian Lam_x, Gam_{k,x,r}, Del_{k,x,r} (x_k=1) and Y_{x,c,k} >= 0 with
  M_{xc} := W_{xc} - Lam_x - sum_k [Gam - T_k(Gam) + D]_{k,x,r_k(c)} - sum_k Y_{xck}^{T_k}  >= 0,
W_{xc} = y[x,a(c)] psi_{o(c)} psi_{o(c)}^dag, T_k = Pauli twirl on party k, D = +Del_{k,x,r} (x_k=1) / -Del_{k,x+e_k,r} (x_k=0).
Any Hermitian values give a valid bound once checked exactly (verification does not trust the solver)."""
import numpy as np, itertools as it, cvxpy as cp, sys, re, time, pickle
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2; psi=np.array([U[o]@ph for o in range(8)])
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),float).reshape(8,8)
PPT='ppt' in sys.argv
pc=lambda c,k:(c>>(2*(2-k)))&3
def rest(c,k): return tuple(pc(c,j) for j in range(3) if j!=k)
Ps=[np.eye(2),np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
def emb(Pm,k): return np.kron(np.kron(Pm if k==0 else np.eye(2),Pm if k==1 else np.eye(2)),Pm if k==2 else np.eye(2))
def twirl(G,k): return sum(emb(Pm,k)@G@emb(Pm,k).conj().T for Pm in Ps)/4
def ptT(X,k): return cp.partial_transpose(X,[2,2,2],k)
Lam={x:cp.Variable((8,8),hermitian=True) for x in range(8)}
Gam={(k,x,r):cp.Variable((8,8),hermitian=True) for k in range(3) for x in range(8) for r in it.product(range(4),repeat=2)}
Del={(k,x,r):cp.Variable((8,8),hermitian=True) for k in range(3) for x in range(8) if B3[x][k]==1 for r in it.product(range(4),repeat=2)}
Y={(x,c,k):cp.Variable((8,8),hermitian=True) for x in range(8) for c in range(64) for k in range(3)} if PPT else {}
cons=[]; 
def flip(x,k): b=list(B3[x]); b[k]^=1; return B3.index(tuple(b))
for x in range(8):
    for c in range(64):
        a=tuple(pc(c,k)>>1 for k in range(3)); o=tuple(pc(c,k)&1 for k in range(3)); po=psi[B3.index(o)]
        Wc=y[x,B3.index(a)]*np.outer(po,po.conj())
        M=Wc-Lam[x]
        for k in range(3):
            G=Gam[k,x,rest(c,k)]; M=M-(G-twirl(G,k))
            M=M-(Del[k,x,rest(c,k)] if B3[x][k]==1 else -Del[k,flip(x,k),rest(c,k)])
            if PPT: M=M-ptT(Y[x,c,k],k)
        cons.append(M>>0)
cons+=[v>>0 for v in Y.values()]
pr=cp.Problem(cp.Maximize(cp.real(sum(cp.trace(Lam[x]) for x in range(8)))),cons)
t=time.time(); pr.solve(solver='SCS',eps=1e-7,max_iters=200000)
print('dual',('NS+PPT' if PPT else 'NS'),'status',pr.status,'value',pr.value,'time',round(time.time()-t),flush=True)
val=lambda d:{k:v.value for k,v in d.items()}
pickle.dump(dict(Lam=val(Lam),Gam=val(Gam),Del=val(Del),Y=val(Y),ppt=PPT),open('h12_dual_%s.pkl'%('ppt' if PPT else 'ns'),'wb'))
