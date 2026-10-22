"""Polish a family-C solution for purity with L-BFGS on a fixed batch of Haar local unitaries (float64)."""
import sys, torch, numpy as np
torch.set_num_threads(1); c=torch.complex128
f=sys.argv[1]; it_=int(sys.argv[2]); torch.manual_seed(123)
def haar(n):
    z=torch.randn(n,n,dtype=c); q,r=torch.linalg.qr(z); d=torch.diagonal(r); return q*(d/d.abs())
def Vfull(Vs,d):
    T=torch.einsum('ab,cd,ef->acebdf',*Vs).reshape(2,d,2,d,2,d,2,d,2,d,2,d).permute(0,2,4,1,3,5,6,8,10,7,9,11)
    return T.reshape(8,d**3,8,d**3)
def buildV(C):
    V=torch.zeros(8,8,8,8,8,8,dtype=c)
    for o in range(8):
        for e in range(8):
            for t in range(8): V[e,o,e^t,o,:,t]=C[o,e,:]
    return V.reshape(8,64,8,64)
C0=torch.tensor(np.load(f))
for k in range(8):
    u,_,vh=torch.linalg.svd(C0[k]); C0[k]=u@vh
samples=[(Vfull([haar(4) for _ in range(3)],2),2) for _ in range(6)]+[(Vfull([haar(2) for _ in range(3)],1),1) for _ in range(6)]
H=torch.zeros(8,8,8,dtype=c,requires_grad=True)
def loss():
    C=C0@torch.matrix_exp(1j*(H+H.conj().transpose(1,2))/2); V=buildV(C); L=0
    for Vl,d in samples:
        M=torch.einsum('ifos,oyix->fysx',V,Vl).reshape(64*d**3,64*d**3)
        L=L+((M@M.conj().T-torch.eye(64*d**3,dtype=c)).abs()**2).sum()
    return L
opt=torch.optim.LBFGS([H],lr=1,max_iter=it_,history_size=50,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-18)
def cl():
    opt.zero_grad(); L=loss(); L.backward(); return L
opt.step(cl)
with torch.no_grad():
    C=C0@torch.matrix_exp(1j*(H+H.conj().transpose(1,2))/2)
print(f,'final loss',float(loss().detach()))
np.save(f.replace('C_','P_'),C.numpy())
