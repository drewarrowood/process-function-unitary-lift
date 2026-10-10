import numpy as np, itertools as it
exec(open('vw.py').read().split("C=lambda")[0])
C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
W=(W_det(C)+W_det(Cb))/2
lam,vec=np.linalg.eigh(W); keep=lam>1e-9; lam,vec=lam[keep],vec[:,keep]; r=len(lam)
dims=[2]*6+[r]; D=64*r; parties=[(0,1),(2,3),(4,5),(6,None)]
w0=sum(np.sqrt(lam[i])*np.kron(vec[:,i],np.eye(r)[i]) for i in range(r))
G=np.zeros((D,D),complex)
for i in range(D):
    v=np.zeros(D);v[i]=1
    G[:,i]=Lperp(np.outer(v,w0.conj()),dims,parties)@w0
ev,U=np.linalg.eigh((G+G.conj().T)/2); B=U[:,ev<1e-8]; m=B.shape[1]
c0=B.conj().T@w0; print('m',m,'|w0 - B c0|',np.linalg.norm(B@c0-w0),flush=True)
H=np.zeros((m*m,m*m),complex)
for a in range(m):
  for b in range(m):
    X=np.zeros((m,m));X[a,b]=1
    H[:,a*m+b]=(B.conj().T@Lperp(B@X@B.conj().T,dims,parties)@B).reshape(-1)
ev2,U2=np.linalg.eigh((H+H.conj().T)/2)
print('dim K',int(np.sum(ev2<1e-8)),flush=True)
np.savez('kern.npz',B=B,c0=c0,K=U2[:,ev2<1e-8],ev2=ev2)
