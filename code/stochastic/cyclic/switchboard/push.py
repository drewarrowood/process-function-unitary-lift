"""Residual-vs-violation curve for the switchboard (family C), using the exact Pauli form of Lemma H.7.1.
For target violation v: minimise R(C) = sum_{o!=o'} sum_{forbidden sigma} |<sigma,C_o C_o'^dag>/8|^2
subject to lambda_max(F_m(C)) >= v, F_m = sum_{(s,i,o) in m} s C_o^dag|i><i|C_o, m a member of facet orbit 82
(bound 0). lambda_max is the facet value at the best source state phi.  Penalty + L-BFGS, float64.
argv: seed v init(rand|lug|file.npy) member_index"""
import sys, json, itertools as it, numpy as np, torch
torch.set_num_threads(1); c=torch.complex128
seed=int(sys.argv[1]); v=float(sys.argv[2]); init=sys.argv[3]; mi=int(sys.argv[4])
torch.manual_seed(seed); rng=np.random.default_rng(seed)
from pauli import PAULI, FORB, B3, IX
sys.path.insert(0,'../../physics/d9')
F82=[(+1,'000','000'),(-1,'000','001'),(-1,'010','001'),(-1,'000','100'),(-1,'010','110'),(-1,'011','111')]
F82=[(s,tuple(map(int,i)),tuple(map(int,o))) for s,i,o in F82]
mem=set()
for pi in it.permutations(range(3)):
    for fi in B3:
        for fo in B3:
            g=lambda w,f:tuple(w[pi[k]]^f[k] for k in range(3))
            mem.add(frozenset((s,g(i,fi),g(o,fo)) for s,i,o in F82))
MEM=sorted([sorted(m) for m in mem]); m=MEM[mi%len(MEM)]
# forbidden projector per pair: R_pair = sum |<sigma,K>|^2/64 ; build as stacked matrices
pairs=[(o,o2) for (o,o2) in FORB if o<o2]
S=[torch.tensor(np.array([PAULI[ab].conj().T for ab in FORB[p]]),dtype=c) for p in pairs]
def unit(H): return torch.matrix_exp(1j*(H+H.conj().transpose(-1,-2))/2)
C0=torch.eye(8,dtype=c).repeat(8,1,1)
if init=='lug':
    lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
    for o in B3:
        P=torch.zeros(8,8,dtype=c)
        for e in B3: P[IX[tuple(a^b for a,b in zip(lug(o),e))],IX[e]]=1
        C0[IX[o]]=P
elif init.endswith('.npy'): C0=torch.tensor(np.load(init),dtype=c)
sc=1.0 if init=='rand' else 0.2
H=(torch.randn(8,8,8,dtype=c)*sc).requires_grad_()
def R(C):
    t=0
    for p,Sp in zip(pairs,S):
        K=C[p[0]]@C[p[1]].conj().T
        t=t+(torch.einsum('nij,ji->n',Sp,K).abs()**2).sum()/64
    return t
def Fm(C):
    F=0
    for s,i,o in m:
        r=C[IX[o]][IX[i]]          # row i of C_o
        F=F+s*torch.outer(r.conj(),r)
    return F
def lmax(C): return torch.linalg.eigvalsh(Fm(C))[-1].real
def loss(mu):
    C=C0@unit(H); return R(C)+mu*torch.relu(v-lmax(C))**2
for mu in [1,10,100,1e3,1e4]:
    opt=torch.optim.LBFGS([H],lr=1,max_iter=400,history_size=50,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-16)
    def cl():
        opt.zero_grad(); L=loss(mu); L.backward(); return L
    opt.step(cl)
with torch.no_grad():
    C=C0@unit(H); r=float(R(C)); lm=float(lmax(C))
np.save('sb_%s_%g_%d_%d.npy'%(init.replace('.npy','').replace('../',''),v,seed,mi),C.numpy())
print(json.dumps(dict(seed=seed,v=v,init=init,member=mi,R=r,lmax=lm)),flush=True)
