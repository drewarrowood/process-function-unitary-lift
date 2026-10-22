"""Direct purity check of the exact counterexample board (built in float64 from the integer phases), independent of
Lemma H.7.1/H.8: induced M for Haar local unitaries with ancilla dims 1,2,3 (30 samples); max |MM^+-1|, |M^+M-1|.
Also: the induced classical process at source phi(x)|0> recomputed by simulating deterministic interventions
f implemented as unitaries with a qubit ancilla (|i,0> -> |f(i), i>), compared with p."""
import json, itertools as it, numpy as np
k=json.load(open('cex_phases.json')); h=np.array([[1,1],[1,-1]])/2**.5; Hd=np.kron(np.kron(h,h),h)
C=np.array([Hd@np.diag(1j**(np.array(k[o])//2))@Hd for o in range(8)])
V=np.zeros((8,8,8,8,8,8),complex)
for o in range(8):
    for e in range(8):
        for t in range(8): V[e,o,e^t,o,:,t]=C[o,e,:]
V=V.reshape(8,64,8,64); T=V.reshape(2,2,2,64,2,2,2,64)
rng=np.random.default_rng(11)
def haar(n):
    z=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
w1=w2=0
for trial in range(30):
    dx=1+trial%3; Us=[haar(2*dx).reshape(2,dx,2,dx) for _ in range(3)]
    M=np.einsum('abcFpqrS,pAaX,qBbY,rCcZ->FABCSXYZ',T,*Us,optimize=True).reshape(64*dx**3,64*dx**3)
    I=np.eye(M.shape[0]); w1=max(w1,abs(M@M.conj().T-I).max()); w2=max(w2,abs(M.conj().T@M-I).max())
print('30 Haar samples, ancilla dims 1-3: max|MM^+-1| %.2e  max|M^+M-1| %.2e'%(w1,w2))
phi=np.zeros(8,complex); phi[3]=2**-.5; phi[4]=np.exp(7j*np.pi/4)*2**-.5
src=np.kron(phi,np.eye(8)[0])
fs=[(0,0),(1,1),(0,1),(1,0)]; p=np.array([[abs(C[o][i]@phi)**2 for o in range(8)] for i in range(8)]); worst=0
for g in it.product(range(4),repeat=3):
    # party k: unitary on (I_k (x) X_k=qubit) -> (O_k (x) Y_k): |i,x> -> |f(i) xor x, i>  (records i in Y)
    Us=[]
    for t in range(3):
        u=np.zeros((2,2,2,2))   # [o,y,i,x]
        for i in range(2):
            for x in range(2): u[fs[g[t]][i]^x,i,i,x]=1
        Us.append(u)
    M=np.einsum('abcFpqrS,pAaX,qBbY,rCcZ->FABCSXYZ',T,*Us,optimize=True).reshape(64,8,64,8)
    out=np.einsum('fys,s->fy',M[:,:,:,0],src)        # ancillas start in 0; Y records the inputs
    py=(abs(out)**2).sum(0)                            # distribution of recorded inputs i
    pred=np.array([p[i,int(''.join(map(str,[fs[g[t]][((i>>(2-t))&1)] for t in range(3)])),2)] for i in range(8)])
    # consistency: P(record i) = p(i | f(i)) for the unique-fixed-point semantics of classical validity
    worst=max(worst,abs(py-pred).max(),abs(py.sum()-1))
print('64 deterministic interventions simulated through V: max |P(i) - p(i|f(i))|, |sum-1| = %.2e'%worst)
