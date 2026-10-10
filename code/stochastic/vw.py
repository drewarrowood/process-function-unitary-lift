import numpy as np, itertools as it, sys
# subsystems order: A_I A_O B_I B_O C_I C_O F'
def W_det(w):
    W=np.zeros((64,64))
    for o in it.product((0,1),repeat=3):
        x=w(o); idx=0
        for k in range(3): idx=idx*4+x[k]*2+o[k]
        W[idx,idx]=1
    return W
def consistent(W):
    D=W.diagonal().reshape([2]*6)  # aI aO bI bO cI cO
    fs=list(it.product((0,1),repeat=2))  # f(x) table
    for f in it.product(fs,repeat=3):
        p=sum(D[x1,f[0][x1],x2,f[1][x2],x3,f[2][x3]] for x1 in (0,1) for x2 in (0,1) for x3 in (0,1))
        if abs(p-1)>1e-9: return False
    return True
def TR(X,dims,sys_):
    # trace-and-replace on subsystem list sys_
    n=len(dims); T=X.reshape(dims+dims)
    for s in sys_:
        d=dims[s]
        tr=np.trace(T,axis1=s,axis2=s+n)  # removes axes
        tr=np.expand_dims(np.expand_dims(tr,s),s+n)
        T=np.broadcast_to(tr,T.shape)/d*np.eye(d).reshape([d if i in (s,s+n) else 1 for i in range(2*n)])
    return T.reshape(X.shape)
def Lperp(X,dims,parties):
    # parties: list of (Isys,Osys or None); P_K = prod_{k in K}(1-O_k) prod_{j notin K}(I_j O_j)
    out=np.zeros_like(X); N=len(parties)
    for r in range(1,N+1):
        for K in it.combinations(range(N),r):
            if any(parties[k][1] is None for k in K): continue
            Y=X
            for j in range(N):
                if j not in K: Y=TR(Y,dims,[s for s in parties[j] if s is not None])
            for k in K: Y=Y-TR(Y,dims,[parties[k][1]])
            out=out+Y
    return out
def dimVW(W):
    lam,vec=np.linalg.eigh(W); keep=lam>1e-9; lam,vec=lam[keep],vec[:,keep]; r=len(lam)
    dims=[2]*6+[r]; D=64*r
    w0=sum(np.sqrt(lam[i])*np.kron(vec[:,i],np.eye(r)[i]) for i in range(r))
    parties=[(0,1),(2,3),(4,5),(6,None)]
    G=np.zeros((D,D),complex)
    for i in range(D):
        v=np.zeros(D);v[i]=1
        G[:,i]=Lperp(np.outer(v,w0.conj()),dims,parties)@w0
    ev=np.linalg.eigvalsh((G+G.conj().T)/2)
    return r,int(np.sum(ev<1e-8))
C=lambda o:(o[2],o[0],o[1]); Cb=lambda o:(1-o[2],1-o[0],1-o[1])
lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
const=lambda o:(0,0,0); chain=lambda o:(0,o[0],o[1])
tests={'lugano':W_det(lug),'mix const+chain':(W_det(const)+W_det(chain))/2,
       'Eex1=(C+Cbar)/2':(W_det(C)+W_det(Cb))/2,'C alone':W_det(C)}
for name,W in tests.items():
    print(name,'consistent',consistent(W),'(rank, dimV_W)',dimVW(W),flush=True)
