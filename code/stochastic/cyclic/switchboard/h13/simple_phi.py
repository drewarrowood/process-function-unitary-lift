"""Find a simple source phi (entries in {0,+-1,+-i}, <=2 nonzero... up to 4) violating a hull facet for the Z_2 board."""
import numpy as np, itertools as it, gzip, sys, json
from xenum import D4, B3
n=int(sys.argv[1]); R=np.load('xreps.npy').astype(int); m=D4[R[n]]
print('phases m_o(z) (i^m):'); print(m)
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T
Hd=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3])/8**.5
U=np.stack([Hd@np.diag(1j**m[o])@Hd for o in range(8)])
best=(0,None,None)
for nnz in (1,2,3,4):
  for S in it.combinations(range(8),nnz):
    for ph in it.product(range(4),repeat=nnz-1):
      phi=np.zeros(8,complex); phi[list(S)]=[1]+[1j**q for q in ph]; phi/=np.linalg.norm(phi)
      p=np.abs(U@phi)**2                       # [o,i]
      v=-(T[:,:64]@p.T.reshape(-1)+T[:,64])/vals.max(0)
      f=v.argmax()
      if v[f]>best[0]+1e-12: best=(v[f],f,(S,ph))
  print(nnz,best,flush=True)
json.dump(dict(board=n,m=m.tolist(),facet=int(best[1]),S=best[2][0],ph=best[2][1],relviol=best[0]),open('min_cex.json','w'))
