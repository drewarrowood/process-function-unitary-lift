"""Independent verification of a candidate X-type board (argv: npy file)."""
import sys, json, itertools as it, numpy as np
sys.path.insert(0,'..'); sys.path.insert(0,'../..')
from pauli import resid
from lemmaC import viol
from common import in_hull, valid, all_pfs
C=np.load(sys.argv[1])
print('unitarity max', max(abs(C[o]@C[o].conj().T-np.eye(8)).max() for o in range(8)))
print('Pauli resid', resid(C), ' H.7.1 viol', viol(C))
# full purity with ancillas: V[i,(o',t'),o,(s,t)] ; random local unitaries with qubit ancilla
V=np.zeros((8,8,8,8,8,8),complex)
for o in range(8):
    for e in range(8):
        for t in range(8): V[e,o,e^t,o,:,t]=C[o,e,:]
V=V.reshape(8,64,8,64)
rng=np.random.default_rng(0)
def haar(n):
    z=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
worst=0
for trial in range(6):
    dx=2 if trial%2 else 1
    Us=[haar(2*dx).reshape(2,dx,2,dx) for _ in range(3)]       # [o,y,i,x]
    T=V.reshape(2,2,2,64,2,2,2,64)
    M=np.einsum('abcFpqrS,pAaX,qBbY,rCcZ->FABCSXYZ',T,*Us,optimize=True).reshape(64*dx**3,64*dx**3)
    worst=max(worst,abs(M@M.conj().T-np.eye(M.shape[0])).max())
print('purity residual (direct, 6 Haar samples incl. qubit ancillas)',worst)
# facet operator, best phi
pfs=all_pfs(); print('PFs',len(pfs))
import gzip
Z=np.load('../../../physics/facets/Z.npy').astype(float); PF=np.load('../../pfs744.npy').reshape(744,-1).astype(float)
T_=np.linalg.lstsq(np.c_[PF,np.ones(744)],Z,rcond=None)[0]
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:')); n=int(L[k].split()[0])
H=np.array([list(map(int,L[k+1+j].split())) for j in range(n)],float); g=(T_[:64]@H[:,:37].T).T.reshape(n,8,8); g0=T_[64]@H[:,:37].T+H[:,37]
Pr=np.array([[np.outer(C[o][i].conj(),C[o][i]) for i in range(8)] for o in range(8)])  # [o,i]
Mf=np.einsum('fio,oiab->fab',g,Pr)+g0[:,None,None]*np.eye(8); ev,evec=np.linalg.eigh(Mf)
f=int(ev[:,0].argmin()); print('most violated facet',f,'lambda_min',ev[f,0])
phi=evec[f][:,0]; p=np.array([[abs(C[o][i]@phi)**2 for o in range(8)] for i in range(8)])
print('validity (min,max sum, min p)',valid(p)); print('L1 distance to conv(744 PFs) by LP',in_hull(p,pfs))
np.save(sys.argv[1].replace('.npy','_phi.npy'),phi); np.save(sys.argv[1].replace('.npy','_p.npy'),p)
