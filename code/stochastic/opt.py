import numpy as np, sys, json
from scipy.optimize import minimize
import fast2, fast3
def search(E,restarts=3,seed=0,maxiter=3000):
    d,supp,r,m,Xs,Lam=fast3.prep(E); T=fast3.forms(Xs,Lam).astype(float)
    used=np.nonzero(np.abs(T).sum(axis=(0,1))>1e-9)[0]; T=T[:,:,used]
    G=np.einsum('aij,j,bij->ab',Xs,Lam,Xs)   # <w_a|w_b>
    W=np.zeros((64,64)); W[supp,supp]=d[supp]
    c0=np.linalg.lstsq(Xs.reshape(m,-1).T,W.ravel(),rcond=None)[0]
    assert np.allclose(np.tensordot(c0,Xs,1),W)
    def f(x):
        C=np.column_stack([c0,x.reshape(m,r-1)])
        Z=np.einsum('abk,bj->ajk',T,C); R=np.einsum('ai,ajk->ijk',C,Z)
        O=C.T@G@C-np.trace(W)*np.eye(r)
        val=np.sum(R**2)+np.sum(O**2)
        gC=2*np.einsum('ijk,ajk->ai',R,Z)+2*np.einsum('jik,abk,bj->ai',R,T,C)*0  # placeholder
        # second term: d/dC_ai of R_jik where i is second index: sum_j R_jik * (C_j^T T_k)_a
        Y=np.einsum('aj,abk->bjk',C,T)          # (C_j^T T_k)_b
        gC=2*np.einsum('ijk,ajk->ai',R,Z)+2*np.einsum('jik,ajk->ai',R,Y)
        gC+=4*(G@C@O)
        return val, gC[:,1:].ravel()
    best=None; rng=np.random.default_rng(seed)
    for s in range(restarts):
        x0=rng.normal(size=m*(r-1))*np.sqrt(np.trace(W)/max(1,np.trace(G)))
        res=minimize(f,x0,jac=True,method='L-BFGS-B',options={'maxiter':maxiter,'gtol':1e-12,'ftol':1e-16})
        if best is None or res.fun<best: best=res.fun
        if best<1e-12: break
    return dict(rank=int(r),dimVW=int(m),min_residual=float(best))
if __name__=='__main__':
    B3=fast2.B3
    def P(w):
        M=np.zeros((8,8))
        for a in B3: M[B3.index(w(a)),B3.index(a)]=1
        return M
    lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
    C_=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
    for n,E in [('lugano',P(lug)),('Eex1',(P(C_)+P(Cb))/2)]:
        print(n,search(E),flush=True)
