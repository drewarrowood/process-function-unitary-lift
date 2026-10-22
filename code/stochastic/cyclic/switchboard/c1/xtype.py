"""X-type boards U_o = Hd diag(exp(i theta_o)) Hd (Hd = 3-qubit Hadamard): spans of X-strings, any number of terms.
Minimise the exact Pauli residual R (H.8.1), optionally at prescribed facet-82 violation v (as push.py).
argv: seed v(0 = purity only) member"""
import sys, json, itertools as it, numpy as np, torch
sys.path.insert(0,'..'); torch.set_num_threads(1); c=torch.complex128
from pauli import PAULI, FORB, B3, IX
seed=int(sys.argv[1]); v=float(sys.argv[2]); mi=int(sys.argv[3]); torch.manual_seed(seed)
h=torch.tensor([[1,1],[1,-1]],dtype=c)/2**.5; Hd=torch.kron(torch.kron(h,h),h)
pairs=[(o,q) for (o,q) in FORB if o<q]
S=[torch.tensor(np.array([PAULI[ab].conj().T for ab in FORB[p]]),dtype=c) for p in pairs]
F82=[(+1,'000','000'),(-1,'000','001'),(-1,'010','001'),(-1,'000','100'),(-1,'010','110'),(-1,'011','111')]
F82=[(s,tuple(map(int,i)),tuple(map(int,o))) for s,i,o in F82]
mem=set()
for pi in it.permutations(range(3)):
    for fi in B3:
        for fo in B3:
            g=lambda w,f:tuple(w[pi[k]]^f[k] for k in range(3)); mem.add(frozenset((s,g(i,fi),g(o,fo)) for s,i,o in F82))
m=sorted([sorted(x) for x in mem])[mi%384]
th=(torch.rand(8,8,dtype=torch.float64)*6.283).requires_grad_()
def U(): return torch.stack([Hd@torch.diag(torch.exp(1j*th[o]).to(c))@Hd for o in range(8)])
def R(C): return sum((torch.einsum('nij,ji->n',Sp,C[p[0]]@C[p[1]].conj().T).abs()**2).sum()/64 for p,Sp in zip(pairs,S))
def lmax(C):
    F=0
    for s,i,o in m: r=C[IX[o]][IX[i]]; F=F+s*torch.outer(r.conj(),r)
    return torch.linalg.eigvalsh(F)[-1].real
for mu in ([0] if v==0 else [1,10,100,1e3,1e4]):
    opt=torch.optim.LBFGS([th],max_iter=600,history_size=50,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-18)
    def cl():
        opt.zero_grad(); C=U(); L=R(C)+(mu*torch.relu(v-lmax(C))**2 if v>0 else 0); L.backward(); return L
    opt.step(cl)
with torch.no_grad(): C=U(); r=float(R(C)); lm=float(lmax(C))
np.save('xt_%g_%d_%d.npy'%(v,seed,mi),C.numpy()); print(json.dumps(dict(seed=seed,v=v,member=mi,R=r,lmax=lm)),flush=True)
