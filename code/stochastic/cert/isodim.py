"""Numerical probe: smallest isotropy loss of an rr-dim complex subspace of V_W, for several rr (isotropy only)."""
import sys, time, torch
sys.path.insert(0,'/workspace/pful-work/code/stochastic/cert')
from common import load
from certsearch import basis
torch.set_num_threads(8)
name=sys.argv[1]; rrs=[int(x) for x in sys.argv[2].split(',')]; steps=int(sys.argv[3])
L,Xs,Lam,r=basis(load(name),torch.device('cpu')); m=Xs.shape[0]
Xc=Xs.to(torch.complex128); Lc=L.to(torch.complex128); sl=Lam.sqrt().to(torch.complex128)
s=torch.linalg.svdvals(torch.einsum('aij,j,bkj->aibk',Xs,Lam,Xs).reshape(m*64,m*64)) # not used
for rr in rrs:
  best=1e9
  for seed in range(2):
    torch.manual_seed(seed); Z=torch.randn(m,rr,dtype=torch.complex128,requires_grad=True)
    opt=torch.optim.Adam([Z],lr=0.02)
    for it in range(steps):
      C,_=torch.linalg.qr(Z); XC=torch.einsum('ai,ajk->ijk',C,Xc)*sl
      M=torch.einsum('ijk,lhk->iljh',XC,XC.conj()).reshape(rr*rr,4096)
      f=((M@Lc.T).abs()**2).sum(); opt.zero_grad(); f.backward(); opt.step()
    best=min(best,float(f))
  print(name,'m',m,'r',r,'rr',rr,'loss',best,flush=True)
