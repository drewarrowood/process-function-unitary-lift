import numpy as np
from common import *
def haar(d,rng):
    z=(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
def purity_resid(V,trials=10,dx=2,seed=0):
    """V[i,f,o,s]; max ||MM^+-1|| over Haar local unitaries (qubit ancillas of dim dx)."""
    rng=np.random.default_rng(seed); dF,dP=V.shape[1],V.shape[3]; worst=0
    for _ in range(trials):
        U=[haar(2*dx,rng).reshape(2,dx,2,dx) for _ in range(3)]  # [o,y,i,x]
        T=V.reshape(2,2,2,dF,2,2,2,dP)
        M=np.einsum('abcFpqrS,pAaX,qBbY,rCcZ->FABCSXYZ',T,*U,optimize=True).reshape(dF*dx**3,dP*dx**3)
        worst=max(worst,np.abs(M@M.conj().T-np.eye(M.shape[0])).max())
    return worst
