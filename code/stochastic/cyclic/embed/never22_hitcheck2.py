import sys,numpy as np
sys.argv=['x','1','0','0']
exec(open('never22_lugU.py').read().split('best=[]')[0])
d=np.load('never22_hit_draw.npy'); rev=int(d[0]); th=d[1:]
V=board(th,rev)
print('V unitary dev',abs(V.conj().T@V-np.eye(64)).max())
def haar(n):
    z=(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def cyc(M,UA,UB,UC):
    t=M.reshape((2,)*12); u=[U.reshape(2,2,2,2) for U in (UA,UB,UC)]
    return np.einsum('abcFGHxyzPQR,xAaD,yBbE,zCcK->FGHABCPQRDEK',t,*u,optimize=True).reshape(64,64)
print('purity: closed loop unitary dev (20 Haar draws):',max(abs(C.conj().T@C-np.eye(64)).max() for C in [cyc(V,haar(4),haar(4),haar(4)) for _ in range(20)]))
P=forms(V); Fm=np.einsum('fr,rst->fst',Ts[:,:64],P)+Ts[:,64,None,None]*np.eye(8)
w,U=np.linalg.eigh(Fm); f=np.argmin(w[:,0]); psi=U[f][:,0]; print('facet idx (within sel)',f,'orbit',cs[f],'viol',-w[f,0])
p=np.real(np.einsum('s,rst,t->r',psi.conj(),P,psi))   # 64 = i*8+o
# affine hull residual
Apf=PF.reshape(744,-1); M=np.c_[Apf,np.ones(744)]
c,res,rk,_=np.linalg.lstsq(M.T,np.r_[p,1],rcond=None); print('rank of PF affine system',rk,'residual of p in aff(PF):',abs(M.T@c-np.r_[p,1]).max())
# validity of p
import itertools as it
pr=p.reshape(8,8); B3=list(it.product((0,1),repeat=3))
print('min p',pr.min(),' col sums',abs(pr.sum(0)-1).max())
dev=0
for hs in it.product(range(4),repeat=3):
    tot=sum(pr[i,B3.index(tuple((hs[k]>>B3[i][k])&1 for k in range(3)))] for i in range(8)); dev=max(dev,abs(tot-1))
print('validity dev over 64 deterministic interventions',dev)
# LP: is p in conv(PF)?
from scipy.optimize import linprog
r=linprog(np.zeros(744),A_eq=np.r_[Apf.T,np.ones((1,744))],b_eq=np.r_[p,1],bounds=(0,None),method='highs'); print('p in conv(PF)? LP status',r.status,r.message)
fi=np.where(sel)[0][f]; print('global facet index',fi,'orbit',canon[fi]); np.save('/tmp/r15/hit_p.npy',p); np.save('/tmp/r15/hit_psi.npy',psi)
