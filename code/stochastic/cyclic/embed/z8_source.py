"""Extract the H.14.2 source vector (class 10515, orbit 16, facet 12406) used by cert_z8.py, saved as z8_source.npy."""
import numpy as np, os
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)),'../switchboard/h13'))
src=open('cert_z8.py').read().split('def certify')[0]; exec(src)
m=R[10515]; zeta=np.exp(2j*np.pi/8)
Hd=np.array([[(-1)**bin(x&y).count('1') for y in range(8)] for x in range(8)])/np.sqrt(8)
Uf=np.stack([Hd@np.diag([zeta**int(m[o][z]) for z in range(8)])@Hd for o in range(8)])
Pf=np.einsum('ois,oit->iost',Uf.conj(),Uf).reshape(64,8,8)
fs=np.nonzero(canon==16)[0]; Fm=np.einsum('fr,rst->fst',Tf[fs,:64],Pf)+Tf[fs,64,None,None]*np.eye(8)
w,vv=np.linalg.eigh(Fm); j=w[:,0].argmin(); print('facet',fs[j],'min eig',w[j,0]); v=vv[j][:,0]
np.save('../../embed/z8_source.npy',v); print('phases',m.tolist())
