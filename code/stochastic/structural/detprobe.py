# Appendix H(B): determinantal probe. dim S <= m - rank K(u) for any nonzero u in a jointly isotropic S.
import sys, torch, numpy as np
sys.path.insert(0,'/workspace/pful-work/code/stochastic/cert')
from common import load; from certsearch import basis
torch.set_num_threads(8); name=sys.argv[1]
L,Xs,Lam,r=basis(load(name),torch.device('cpu')); m=Xs.shape[0]
Y=torch.einsum('aij,j,bkj->abik',Xs,Lam,Xs).reshape(m*m,4096)
T=(Y@L.T)
U,s,Vh=torch.linalg.svd(T,full_matrices=False); k=int((s>1e-9*s[0]).sum())
F=(U[:,:k]*s[:k]).T.reshape(k,m,m)
print(name,'m',m,'r',r,'independent forms',k,flush=True)
Fc=F.to(torch.complex128)
# common radical R = {u : K(u)=0}; restrict u to R-perp
Mrad=F.permute(1,0,2).reshape(m,-1); sr=torch.linalg.svdvals(Mrad); dR=int((sr<1e-9*sr[0]).sum())
Ur,_,_=torch.linalg.svd(Mrad); Bp=Ur[:,:m-dR].to(torch.complex128)
print('common radical dim',dR,flush=True)
def K(u): return torch.einsum('a,tab->tb',u.conj(),Fc)
def iso(u): return (torch.einsum('a,tab,b->t',u.conj(),Fc,u).abs()**2).sum()
res=[]; push=len(sys.argv)>3
for seed in range(int(sys.argv[2])):
  torch.manual_seed(seed); z=torch.randn(m-dR,dtype=torch.complex128,requires_grad=True); opt=torch.optim.Adam([z],lr=0.01)
  for it in range(2000):
    u=Bp@(z/z.norm()); loss=1e3*iso(u)
    if push: loss=loss+torch.linalg.svdvals(K(u))[60:].sum()
    opt.zero_grad(); loss.backward(); opt.step()
  u=(Bp@(z/z.norm())).detach(); sv=torch.linalg.svdvals(K(u))
  rk=int((sv>1e-6*sv[0]).sum()); res.append(rk)
  print('seed',seed,'iso',float(iso(u)),'numrank K(u)',rk,'sv[0,20,40,50,55,58,59,60,62,66,70]',[float('%.2g'%sv[j]) for j in (0,20,40,50,55,58,59,60,62,66,70)],flush=True)
print('min numrank',min(res),'=> any isotropic subspace through such u has dim <=',m-min(res))
