"""H.13 [numerical]: for every Z_4 X-type pure switchboard (xboards_z4.npy), max over source states of the violation
of each of the 29344 PF-hull facets: viol = -lambda_min(sum g[i,o] P_{o,i} + g0), relative to facet range on PFs."""
import numpy as np, itertools as it, gzip, json, sys
from xenum import D4, B3
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float); G=np.load(F+'G.npy')
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]                              # [744,nf] facet values on PFs
tight=(np.abs(vals)<1e-6).T; Ginv=np.argsort(G,axis=1); inv={}; canon=[]
for s in range(0,len(Hm),2000):
    K=np.packbits(tight[s:s+2000][:,Ginv],axis=2); V=np.ascontiguousarray(K).view(np.dtype((np.void,K.shape[2])))[...,0]
    for m in np.sort(V,axis=1)[:,0]: canon.append(inv.setdefault(m.tobytes(),len(inv)))
canon=np.array(canon); 
A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T   # [nf,65]: facet = g.p+g0
assert np.abs(A@T.T-vals).max()<1e-8
rng=vals.max(0); Tn=T/rng[:,None]
Hd=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3])/8**.5
N=int(sys.argv[1]);sh=int(sys.argv[2]);ns=int(sys.argv[3])
boards=np.load('xreps_z%d.npy'%N).astype(np.int64)[sh::ns]
zeta=np.exp(2j*np.pi/N)
out=np.zeros((len(boards),len(inv)),np.float32); best=[]
for n,b in enumerate(boards):
    U=np.stack([Hd@np.diag(zeta**b[o])@Hd for o in range(8)])          # [o,i,s]
    P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)               # P_{o,i}=U^dag|i><i|U, index i*8+o
    Fm=np.einsum('fr,rst->fst',Tn[:,:64],P)+Tn[:,64,None,None]*np.eye(8)
    v=-np.linalg.eigvalsh(Fm)[:,0]
    np.maximum.at(out[n],canon,v.astype(np.float32))
    if n%100==0: print(n,v.max(),flush=True)
np.save('xviol_z%d_%d.npy'%(N,sh),out)
