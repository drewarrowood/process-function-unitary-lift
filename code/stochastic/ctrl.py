import numpy as np, itertools as it, numpy.linalg as la, sys
exec(open('vw.py').read().split("C=lambda")[0])
def bound(W):
    lam,vec=la.eigh(W); keep=lam>1e-9; lam,vec=lam[keep],vec[:,keep]; r=len(lam)
    dims=[2]*6+[r]; D=64*r; parties=[(0,1),(2,3),(4,5),(6,None)]
    w0=sum(np.sqrt(lam[i])*np.kron(vec[:,i],np.eye(r)[i]) for i in range(r))
    G=np.zeros((D,D),complex)
    for i in range(D):
        v=np.zeros(D);v[i]=1; G[:,i]=Lperp(np.outer(v,w0.conj()),dims,parties)@w0
    ev,U=la.eigh((G+G.conj().T)/2); B=U[:,ev<1e-8]; m=B.shape[1]
    Hs=np.zeros((m*m,m*m),complex)
    for a in range(m):
      for b in range(m):
        X=np.outer(B[:,a],B[:,b].conj())
        Hs[:,a*m+b]=(B.conj().T@Lperp(X,dims,parties)@B).reshape(-1)
    e2,U2=la.eigh((Hs+Hs.conj().T)/2); Fs=U2[:,e2>1e-8]
    best=m
    for t in range(Fs.shape[1]):
        A=Fs[:,t].reshape(m,m).conj().T
        for Hm in ((A+A.conj().T)/2,(A-A.conj().T)/2j):
            e=la.eigvalsh(Hm); best=min(best,np.sum(abs(e)<1e-9)+min(np.sum(e>1e-9),np.sum(e<-1e-9)))
    return r,m,Fs.shape[1],best
lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
print('lugano (rank, dimVW, #constraints, isotropic bound)',bound(W_det(lug)),flush=True)
