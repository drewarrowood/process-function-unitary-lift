import sys,itertools as it
exec(open('h21_inst_search.py').read().split("if __name__=='__main__':")[0])
def vdev(p):
    worst=0
    for g in it.product(range(4),repeat=3):
        fp=sum(p[i,sum(((g[k]>>B3[i][k])&1)<<(2-k) for k in range(3))] for i in range(8)); worst=max(worst,abs(fp-1))
    return worst
for R in range(8):
  out=[]
  for w in (4,10,13):
    npar,value=build(maxi[w],R); th=torch.tensor(np.random.default_rng(R+w).normal(size=npar))
    _,G=value(th,torch.zeros(8,8),0.0,eig=True)
    rho=torch.randn(G.shape[-1],dtype=torch.complex128); rho/=torch.linalg.norm(rho)
    p=torch.einsum('p,iopq,q->io',rho.conj(),G,rho).real.numpy(); out.append(round(vdev(p),4))
  print('R',R,out)
