import numpy as np, itertools as it, numpy.linalg as la, json, sys, time
def TRb(T,dims,s):
    # T: (batch, D, D); trace-and-replace subsystem s
    n=len(dims); b=T.shape[0]; X=T.reshape((b,)+tuple(dims)+tuple(dims))
    tr=np.trace(X,axis1=1+s,axis2=1+s+n)            # (b, dims\s, dims\s)
    tr=np.expand_dims(np.expand_dims(tr,1+s),1+s+n)/dims[s]
    eye=np.eye(dims[s],dtype=T.dtype).reshape([1]+[dims[s] if i in (s,s+n) else 1 for i in range(2*n)])
    return (tr*eye).reshape(T.shape)
def Lperp(T,dims,parties):
    out=np.zeros_like(T); N=len(parties)
    for r in range(1,N+1):
        for K in it.combinations(range(N),r):
            if any(parties[k][1] is None for k in K): continue
            Y=T
            for j in range(N):
                if j not in K:
                    for s in parties[j]:
                        if s is not None: Y=TRb(Y,dims,s)
            for k in K: Y=Y-TRb(Y,dims,parties[k][1])
            out+=Y
    return out
def analyse(E, chunk=32, tol=1e-7):
    # E[x,a] 8x8 conditional probs; W = sum E[x,a] |a><a|_O |x><x|_I  ordered A_I A_O B_I B_O C_I C_O
    B3=list(it.product((0,1),repeat=3)); diag=np.zeros(64)
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            idx=0
            for k in range(3): idx=idx*4+x[k]*2+a[k]
            diag[idx]=E[xi,ai]
    supp=np.nonzero(diag>1e-12)[0]; r=len(supp); D=64*r; dims=[2]*6+[r]
    parties=[(0,1),(2,3),(4,5),(6,None)]
    w0=np.zeros(D,complex)
    for i,p in enumerate(supp): w0[p*r+i]=np.sqrt(diag[p])
    G=np.zeros((D,D),complex)
    for c0 in range(0,D,chunk):
        n=min(chunk,D-c0); T=np.zeros((n,D,D),complex)
        for j in range(n): T[j,c0+j,:]=w0.conj()
        G[:,c0:c0+n]=(Lperp(T,dims,parties)@w0).T
    ev,U=la.eigh((G+G.conj().T)/2); Bm=U[:,ev<tol]; m=Bm.shape[1]
    res={'rank':r,'dimVW':m,'nec_ok':bool(m>=r)}
    if m<r: return res
    Hs=np.zeros((m*m,m*m),complex)
    for a in range(m):
        T=np.einsum('i,jb->bij',Bm[:,a],Bm.conj())   # (m, D, D): b_a b_b^dagger
        Y=Lperp(T,dims,parties)
        Hs[:,a*m:(a+1)*m]=np.einsum('ia,bij,jc->acb',Bm.conj(),Y,Bm).reshape(m*m,m)
    e2,U2=la.eigh((Hs+Hs.conj().T)/2); Fs=U2[:,e2>tol]
    best=m
    for t in range(Fs.shape[1]):
        A=Fs[:,t].reshape(m,m)
        for Hm in ((A+A.conj().T)/2,(A-A.conj().T)/2j):
            e=la.eigvalsh(Hm); best=min(best,int(np.sum(abs(e)<1e-9)+min(np.sum(e>1e-9),np.sum(e<-1e-9))))
    res.update(ncons=int(Fs.shape[1]),iso_bound=best,ruled_out=bool(best<r))
    return res
if __name__=='__main__':
    B3=list(it.product((0,1),repeat=3))
    def P(w):
        M=np.zeros((8,8))
        for a in B3: M[B3.index(w(a)),B3.index(a)]=1
        return M
    C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
    t=time.time(); print(analyse((P(C)+P(Cb))/2), time.time()-t)
