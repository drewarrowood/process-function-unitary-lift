import sys, torch
sys.path.insert(0,'/workspace/pful-work/code/stochastic/cert')
from common import load
from certsearch import basis
torch.set_num_threads(2)
L,Xs,Lam,r=basis(load('orbit8'),torch.device('cpu')); m=Xs.shape[0]
Xc=Xs.to(torch.complex128); Lc=L.to(torch.complex128); sl=Lam.sqrt().to(torch.complex128)
def f(u):
    u=u/u.norm(); XC=torch.einsum('a,ajk->jk',u,Xc)*sl
    return float(((Lc@(XC@XC.conj().T).reshape(-1)).abs()**2).sum())
g=torch.Generator().manual_seed(0)
v=[f(torch.randn(m,dtype=torch.complex128,generator=g)) for _ in range(50)]
print('m',m,'random unit u: isotropy loss min %.3g median %.3g'%(min(v),sorted(v)[25]))
