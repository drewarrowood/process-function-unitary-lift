"""Try to snap a pure X-type board to phases that are multiples of pi/N (exact cyclotomic candidate),
keeping a hull violation. argv: start.npy N seed. Facet operator of facet f (normaliz index) kept <= -margin."""
import sys, json, gzip, numpy as np, torch
sys.path.insert(0,'..'); torch.set_num_threads(1); c=torch.complex128
from pauli import PAULI, FORB
start=sys.argv[1]; N=int(sys.argv[2]); seed=int(sys.argv[3]); fidx=int(sys.argv[4]) if len(sys.argv)>4 else 16504
torch.manual_seed(seed)
Z=np.load('../../../physics/facets/Z.npy').astype(float); PF=np.load('../../pfs744.npy').reshape(744,-1).astype(float)
T_=np.linalg.lstsq(np.c_[PF,np.ones(744)],Z,rcond=None)[0]
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hf=np.array(list(map(int,L[k+1+fidx].split())),float); g=torch.tensor((T_[:64]@Hf[:37]).reshape(8,8)); g0=float(T_[64]@Hf[:37]+Hf[37])
h=torch.tensor([[1,1],[1,-1]],dtype=c)/2**.5; Hd=torch.kron(torch.kron(h,h),h)
C0=np.load(start); h_=np.array([[1,1],[1,-1]])/2**.5; Hn=np.kron(np.kron(h_,h_),h_)
th0=np.array([np.angle(np.diag(Hn@C0[o]@Hn)) for o in range(8)])
th=torch.tensor(th0+0.0*np.random.default_rng(seed).normal(size=(8,8)),requires_grad=True)
pairs=[(o,q) for (o,q) in FORB if o<q]; S=[torch.tensor(np.array([PAULI[ab].conj().T for ab in FORB[p]]),dtype=c) for p in pairs]
def U(): return torch.stack([Hd@torch.diag(torch.exp(1j*th[o]).to(c))@Hd for o in range(8)])
def R(C): return sum((torch.einsum('nij,ji->n',Sp,C[p[0]]@C[p[1]].conj().T).abs()**2).sum()/64 for p,Sp in zip(pairs,S))
def fmin(C):
    M=torch.einsum('io,oiab->ab',g.to(c),torch.einsum('oia,oib->oiab',C.conj(),C))+g0*torch.eye(8,dtype=c)
    return torch.linalg.eigvalsh(M)[0]
for mu in [1e-3,1e-2,1e-1,1,10]:
    opt=torch.optim.LBFGS([th],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-18)
    def cl():
        opt.zero_grad(); C=U(); snapl=(torch.sin(N*(th-th[:,:1])/2)**2).sum()
        l=R(C)*1e3+mu*snapl+10*torch.relu(fmin(C)+0.02)**2; l.backward(); return l
    opt.step(cl)
with torch.no_grad():
    C=U(); q=((th-th[:,:1])*N/np.pi).numpy()
print(json.dumps(dict(N=N,seed=seed,R=float(R(C)),fmin=float(fmin(C)),snap_err=float(np.abs(q-np.round(q)).max()),ints=np.round(q).astype(int).tolist())))
np.save('snap_%d_%d.npy'%(N,seed),C.numpy())
