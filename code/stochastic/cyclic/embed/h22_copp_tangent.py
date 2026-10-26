"""Round 22 (H.29.1): tangent space of the valid set of classical-output pure processes (COPP) at sample points.
dim T = 512 - rank(Hessian of pen) at a valid point (pen is a sum of squares, Hessian = 2 J^T J).  Compares with the
dimension of the obvious moves: right multiplication by a common unitary (absorbed by psi), left local unitaries, and the
parameters of the family the point came from."""
import sys, json, numpy as np, torch
from h22_copp import *
from h20_common import B3, others
from scipy.stats import unitary_group
torch.set_num_threads(4)
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def herm(x):
    A=torch.complex(x[:,:64].reshape(8,8,8),x[:,64:].reshape(8,8,8)); return (A+A.conj().transpose(1,2))/2
def herm64(y):   # 64 real parameters per o -> Hermitian 8x8 (basis: diag, Re and Im of the upper triangle)
    iu=torch.triu_indices(8,8,1); H=torch.zeros(y.shape[0],8,8,dtype=torch.complex128)
    H=H+torch.diag_embed(y[:,:8].to(torch.complex128))
    up=torch.zeros(y.shape[0],8,8,dtype=torch.complex128); up[:,iu[0],iu[1]]=torch.complex(y[:,8:36],y[:,36:64])
    return H+up+up.conj().transpose(1,2)
def rank_at(U0):
    U0=torch.tensor(U0)
    g=lambda y: resid(U0@torch.linalg.matrix_exp(1j*herm64(y.reshape(8,64))))
    J=torch.autograd.functional.jacobian(g,torch.zeros(512)).numpy()
    s=np.linalg.svd(J,compute_uv=False)
    return int((s>1e-7*s.max()).sum()), float(pen(U0))
def pb(w,t=None,frames=True):
    t=rng.uniform(0,2*np.pi,(3,2,4)) if t is None else t
    Fr=[unitary_group.rvs(2,random_state=rng) if frames else np.eye(2) for k in range(3)]; Ef=np.kron(np.kron(Fr[0],Fr[1]),Fr[2])
    return np.array([Ef@np.diag([np.exp(1j*sum(t[k,B3[o][k],w[k][others(k,a)]] for k in range(3))) for a in range(8)]) for o in range(8)])
def fwd(w):
    Us=[[unitary_group.rvs(2,random_state=rng) for x in range(4)] for k in range(3)]
    return np.array([np.kron(np.kron(Us[0][w[0][others(0,o)]],Us[1][w[1][others(1,o)]]),Us[2][w[2][others(2,o)]]) for o in range(8)])
for name,U in [('phase board w4 (random phases, frames)',pb(maxi[4])),('phase board w10',pb(maxi[10])),('phase board w13 (single-block)',pb(maxi[13])),
               ('forward lift w4 (random qubit node unitaries)',fwd(maxi[4])),('forward lift w13',fwd(maxi[13])),
               ('trivial U_o = 1',np.array([np.eye(8,dtype=complex)]*8))]:
    r,p0=rank_at(U); print(f'{name}: pen {p0:.1e}, rank {r}, tangent dim {512-r}',flush=True)
