"""Round 26 (H.33.3): solve the Hermitian SOS relaxation for one orbit, save the Gram blocks Q_S (small npz in /tmp), print spectra.
usage: orbit out.npz   (env FIXG: fix gamma to this value instead of maximising)"""
import sys, os, numpy as np
from h26_hsos import solve, Tn, canon
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0]); T=Tn[f,:64].reshape(8,8); c=float(Tn[f,64])
n,K,st,g,t,Qs=solve(T,c,range(8),float(os.environ.get('EPS','1e-9')))
print(f'orbit {orb}: {st} gamma*={g} {t:.0f}s',flush=True)
Q=np.array([q.value for q in Qs]); np.savez_compressed(sys.argv[2],Q=Q,g=g)
for S in range(8):
    e=np.linalg.eigvalsh(Q[S]); print(S, 'min %.2e max %.2e'%(e[0],e[-1]), 'n<1e-6:',(e<1e-6).sum(),'n<1e-4:',(e<1e-4).sum(), 'trace %.3f'%e.sum(),flush=True)
