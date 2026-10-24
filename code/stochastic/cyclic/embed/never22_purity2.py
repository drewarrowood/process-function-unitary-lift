"""Round 15, H.22.2 addendum: numerical purity check of the orbit-53/79 board never22_best2.npy (closed loop with Haar local unitaries
on agent qubit + ancilla qubit is unitary).  Purity itself: rg_lugU (fleshing-out, CITED step) + time reversal + local frames."""
import sys,numpy as np
sys.argv=['x','1','0','0']
exec(open('never22_lugU.py').read().split('best=[]')[0])
d=np.load('never22_best2.npy'); rev=int(d[0]); V=board(d[1:],rev)
print('V unitary dev %.1e'%abs(V.conj().T@V-np.eye(64)).max())
r=np.random.default_rng(5)
def haar(n):
    z=(r.normal(size=(n,n))+1j*r.normal(size=(n,n)))/np.sqrt(2); q,rr=np.linalg.qr(z); return q*(np.diag(rr)/abs(np.diag(rr)))
def cyc(M,UA,UB,UC):
    t=M.reshape((2,)*12); u=[U.reshape(2,2,2,2) for U in (UA,UB,UC)]
    return np.einsum('abcFGHxyzPQR,xAaD,yBbE,zCcK->FGHABCPQRDEK',t,*u,optimize=True).reshape(64,64)
print('closed loop unitary dev (20 Haar draws): %.1e'%max(abs(C.conj().T@C-np.eye(64)).max() for C in [cyc(V,haar(4),haar(4),haar(4)) for _ in range(20)]))
for j in range(3):
    ev=np.linalg.eigvals(u2(d[1+4*j:5+4*j])); print('node',j,'eigenphase gap / pi = %.5f'%(abs(np.angle(ev[0]/ev[1]))/np.pi))
