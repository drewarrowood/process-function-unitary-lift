"""Round 32 probe: low-energy structure of M(a,t) for orbit 28 (p = 0). Rotated basis phi = R^T psi, R = (x)_k [[c,-s],[s,c]]."""
import numpy as np, torch, sys
from h24_lugsearch import Mmat
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]) if len(sys.argv)>1 else 28
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
def Mb(a,t):
    th=torch.tensor(np.c_[a,t,np.zeros((len(a),3))]); return Mmat(th,Tf,cf).numpy()
def Rm(t):
    out=[]
    for tt in t:
        R=np.ones((1,1))
        for k in range(3):
            c,s=np.cos(tt[k]/2),np.sin(tt[k]/2); R=np.kron(R,np.array([[c,-s],[s,c]]))
        out.append(R)
    return np.array(out)
rng=np.random.default_rng(0); N=20000
a=rng.uniform(0,2*np.pi,(N,3)); t=rng.uniform(0,np.pi,(N,3))
M=Mb(a,t); R=Rm(t); Mp=np.einsum('bzi,bzw,bwj->bij',R,M,R)
L=[0,1]; H=[2,3,4,5,6,7]
lh=np.linalg.eigvalsh(Mp[:,H][:,:,H])[:,0]; ev=np.linalg.eigvalsh(M)
print('lambda_min(M_HH) min',lh.min(),'lambda3(M) min',ev[:,2].min(),'lambda1 min',ev[:,0].min())
print('|M_LH| max',np.abs(Mp[:,L][:,:,H]).max())
np.set_printoptions(linewidth=220,precision=4,suppress=True)
print(np.round(Mp[0]*384,3))
