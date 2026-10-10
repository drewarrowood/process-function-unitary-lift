import numpy as np, itertools as it, numpy.linalg as la
B3=list(it.product((0,1),repeat=3))
def TR(X,s):
    T=X.reshape([2]*12); tr=np.trace(T,axis1=s,axis2=s+6)
    tr=np.expand_dims(np.expand_dims(tr,s),s+6)/2
    e=np.eye(2).reshape([2 if i in (s,s+6) else 1 for i in range(12)])
    return (tr*e).reshape(64,64)
def Lperp3(X):
    out=np.zeros_like(X); parties=[(0,1),(2,3),(4,5)]
    for r in (1,2,3):
        for K in it.combinations(range(3),r):
            Y=X
            for j in range(3):
                if j not in K: Y=TR(TR(Y,parties[j][0]),parties[j][1])
            for k in K: Y=Y-TR(Y,parties[k][1])
            out=out+Y
    return out
# explicit real superoperator 4096x4096 (acts identically on real/imag parts)
L=np.zeros((4096,4096))
for i in range(4096):
    e=np.zeros(4096); e[i]=1; L[:,i]=Lperp3(e.reshape(64,64)).ravel()
def diagW(E):
    d=np.zeros(64)
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            idx=0
            for k in range(3): idx=idx*4+x[k]*2+a[k]
            d[idx]=E[xi,ai]
    return d
def null(M,tol=1e-9):
    u,s,vh=la.svd(M); rk=int(np.sum(s>tol*max(1,s[0]) )) ; return vh[rk:].conj().T, s
def analyse(E):
    d=diagW(E); supp=np.nonzero(d>1e-12)[0]; r=len(supp)
    # unknown X (64 x r) placed in columns supp; vec index (row, k)
    emb=np.zeros((4096,64*r))
    for k,p in enumerate(supp):
        for row in range(64): emb[row*64+p, row*r+k]=1
    N,_=null(L@emb); m=N.shape[1]
    res={'rank':r,'dimVW':m,'nec_ok':m>=r}
    if m<r: return res
    Xs=[(emb@N[:,a]).reshape(64,64) for a in range(m)]
    Lam=np.zeros(64); Lam[supp]=1/d[supp]
    # constraint functionals on coefficient matrices c (m x m): sum_ab c_a conj(c_b) Lperp(X_a Lam X_b^dag)
    T=np.array([[ (L@(Xs[a]@np.diag(Lam)@Xs[b].conj().T).ravel()) for b in range(m)] for a in range(m)])  # (m,m,4096)
    Mt=T.reshape(m*m,4096).T            # 4096 x m^2 : linear map on vec(c c^dag)
    u,s,vh=la.svd(Mt,full_matrices=False); rk=int(np.sum(s>1e-9*s[0])); Fs=vh[:rk]   # row space = constraint forms
    best=m
    for t in range(rk):
        A=Fs[t].reshape(m,m)
        for Hm in ((A+A.conj().T)/2,(A-A.conj().T)/2j):
            e=la.eigvalsh(Hm); best=min(best,int(np.sum(abs(e)<1e-9)+min(np.sum(e>1e-9),np.sum(e<-1e-9))))
    res.update(ncons=rk,iso_bound=best,ruled_out=best<r)
    return res
if __name__=='__main__':
    import time
    def P(w):
        M=np.zeros((8,8))
        for a in B3: M[B3.index(w(a)),B3.index(a)]=1
        return M
    C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
    lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
    for n,E in [('Eex1',(P(C)+P(Cb))/2),('lugano',P(lug))]:
        t=time.time(); print(n,analyse(E),round(time.time()-t,1),flush=True)
