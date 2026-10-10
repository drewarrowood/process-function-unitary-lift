import numpy as np
d=np.load('kern.npz'); ev2=d['ev2']
H=None
import numpy.linalg as la
# reconstruct orthocomplement of K from saved eigvecs? recompute: we saved only K; get complement via QR
K=d['K']; m=27
Q,_=la.qr(K,mode='complete') if False else (None,None)
P=np.eye(m*m)-K@K.conj().T
u,s,vh=la.svd(P); Fs=u[:,s>0.5]   # basis of K-perp
print('codim',Fs.shape[1])
# constraint: Tr(F^dagger X)=0 for X=u v^dagger  <=> v^dagger F^dagger... form: <F,X>=sum conj(F_ab) u_a conj(v_b)
best=99
for t in range(Fs.shape[1]):
    F=Fs[:,t].reshape(m,m).conj()   # form B(u,v)= sum F_ab u_a conj(v_b) = v^H F^T u
    A=F.T
    for Hm in ((A+A.conj().T)/2,(A-A.conj().T)/2j):
        e=la.eigvalsh(Hm); n0=np.sum(abs(e)<1e-9); npos=np.sum(e>1e-9); nneg=np.sum(e<-1e-9)
        best=min(best,n0+min(npos,nneg))
print('max isotropic dim bound over single forms',best)
