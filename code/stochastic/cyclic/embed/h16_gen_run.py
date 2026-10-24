import sys, numpy as np, torch, time
sys.argv=[sys.argv[0]]+sys.argv[1:]
from h16_gen_search import *
from h16_lugboard import board
seed=int(sys.argv[1]); iters=int(sys.argv[2]); mode=sys.argv[3]
rng=np.random.default_rng(seed); torch.manual_seed(seed)
if mode=='lug': V0=torch.tensor(board(rng.uniform(0,2*np.pi,30),seed%2))
elif mode=='id': V0=torch.eye(64,dtype=torch.complex128)
else:
    from scipy.stats import unitary_group; V0=torch.tensor(unitary_group.rvs(64,random_state=seed))
H=torch.zeros(64,64,dtype=torch.float64,requires_grad=True); G=torch.zeros(64,64,dtype=torch.float64,requires_grad=True)
with torch.no_grad(): H.normal_(0,0.05); G.normal_(0,0.05)
opt=torch.optim.Adam([H,G],lr=float(sys.argv[4]) if len(sys.argv)>4 else 0.01)
def V_of():
    M=torch.complex(H+H.T,G-G.T)   # Hermitian
    return V0@torch.linalg.matrix_exp(1j*M)
t0=time.time()
for t in range(iters):
    mu=10**(1+4*t/iters)
    V=V_of(); v=violations(V); pen=penalty(V)
    sm=torch.logsumexp(200*v,0)/200
    loss=-sm+mu*pen
    opt.zero_grad(); loss.backward(); opt.step()
    if t%200==0 or t==iters-1:
        print(f'{t} mu={mu:.1e} maxviol={float(v.max()):+.6f} pen={float(pen):.3e} {time.time()-t0:.0f}s',flush=True)
V=V_of().detach(); np.save(f'h16_gen_{mode}_{seed}.npy',V.numpy())
v=violations(V); print('FINAL',seed,mode,float(v.max()),float(penalty(V)),'orbits',sorted(set(cs[(v>1e-4).numpy()].tolist())))
