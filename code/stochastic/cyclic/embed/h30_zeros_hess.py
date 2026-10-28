"""Round 30: finite-difference Hessian rank of lambda_min at saved zeros (/tmp/r30/zeros{orb}.npy) and angle statistics. usage: orbit"""
import sys, numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
Z=torch.tensor(np.load(f'/tmp/r30/zeros{orb}.npy'))
ev=torch.linalg.eigvalsh(Mmat(Z,Tf,cf)).numpy(); mult=(ev<1e-8).sum(1)
h=1e-3; E=torch.eye(9)*h; ranks=[]
for b in range(min(len(Z),400)):
    z=Z[b]; pts=[z]+[z+E[i]+E[j] for i in range(9) for j in range(9)]+[z+E[i]-E[j] for i in range(9) for j in range(9)]+[z-E[i]+E[j] for i in range(9) for j in range(9)]+[z-E[i]-E[j] for i in range(9) for j in range(9)]
    v=lam(torch.stack(pts),Tf,cf).numpy(); pp,pm,mp,mm=[v[1+81*q:1+81*(q+1)].reshape(9,9) for q in range(4)]
    H=(pp-pm-mp+mm)/(4*h*h); H=(H+H.T)/2; e=np.linalg.eigvalsh(H); ranks.append((mult[b],int((e>1e-3).sum()),round(float(e.max()),3)))
from collections import Counter
print(Counter((m,r) for m,r,_ in ranks))
w=lambda a: np.angle(np.exp(1j*a)); Zn=Z.numpy()
for name,sl in (('a',slice(0,3)),('t',slice(3,6)),('p',slice(6,9))):
    v=w(Zn[:,sl])
    for k in range(3):
        print(f'{name}{k}: ~0 {(np.abs(v[:,k])<1e-4).mean():.2f} ~pi {(np.abs(np.abs(v[:,k])-np.pi)<1e-4).mean():.2f} ~pi/2 {(np.abs(np.abs(v[:,k])-np.pi/2)<1e-4).mean():.2f}')
