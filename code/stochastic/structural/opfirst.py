"""H.6 numerics: operator-level firstness in source-sink lifts (C.1) of PF blends.
For Lugano (single PF) and the H.5 blend p=1/4[a=b+c+y+z]:
 (1) operator-first test: does any output (incl. own) influence I_k through the open unitary V?
     Choi test J_{I_k,P,O} == Tr_O J (x) 1_O / d_O.
 (2) purity of the 'k-open' bipartite map (k's slot replaced by a swap): always unitary for a pure process.
 (3) classical: is k marginally first, and are the conditionals q_{a,x} valid bipartite processes?
"""
import itertools, numpy as np
rng = np.random.default_rng(0)
B3 = list(itertools.product([0,1],repeat=3))

def lift(pfs):
    J=len(pfs); N=J*8*8
    # in index (j,e(3),o(3)), out index (i(3),j,o(3))
    V=np.zeros((N,N))
    for j,w in enumerate(pfs):
        for e in B3:
            for o in B3:
                i=tuple((w(o)[k]+e[k])%2 for k in range(3))
                inn=np.ravel_multi_index((j,)+e+o,(J,)+(2,)*6)
                out=np.ravel_multi_index(i+(j,)+o,(2,2,2,J,2,2,2))
                V[out,inn]=1
    return V.reshape((2,2,2,J,2,2,2, J,2,2,2,2,2,2))  # iA iB iC | j oA oB oC || j eA eB eC oA oB oC

def opfirst(V,k,J):
    # channel (P=(j,e),O) -> I_k ; rest of outputs traced
    T=np.moveaxis(V,k,0).reshape(2,-1,J*8*8)        # i_k, rest, in
    Jc=np.einsum('arn,brm->anbm',T,T.conj())          # (i_k,in),(i_k',in')
    Jc=Jc.reshape(2,J*8,8,2,J*8,8)
    TrO=np.einsum('apobqo->apbq',Jc)/8
    pred=np.einsum('apbq,or->apobqr',TrO,np.eye(8))
    return np.abs(Jc-pred).max()

def haar(d):
    z=(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))

def open_purity(V,k,J,trials=5):
    """close the two other slots with random unitaries (qubit ancillas); party k gets a SWAP (open slot)."""
    worst=0
    for _ in range(trials):
        Us=[]
        for m in range(3):
            if m==k:
                U=np.zeros((2,2,2,2))
                for i in range(2):
                    for x in range(2): U[x,i,i,x]=1   # U[o,y,i,xanc]: o<-xanc, y<-i
            else: U=haar(4).reshape(2,2,2,2)          # U[o,y,i,xanc]
            Us.append(U)
        # V[iA,iB,iC,jF,oFA,oFB,oFC, j,eA,eB,eC,oA,oB,oC]
        M=np.einsum('abcJPQRjefgxyz,xAaX,yBbY,zCcZ->JPQRABCjefgXYZ',V,*Us,optimize=True)
        d=M.shape[0]*8*8; M=M.reshape(d,d)
        worst=max(worst,np.abs(M@M.conj().T-np.eye(d)).max())
    return worst

def classical(pfs,wts):
    p=np.zeros((2,)*6)  # a b c x y z
    for w,q in zip(pfs,wts):
        for o in B3: p[w(o)+o]+=q
    return p

FUN=list(itertools.product([0,1],repeat=2))
def valid2(q):  # q[b,c,y,z]
    return [sum(q[b,c,f[b],g[c]] for b in range(2) for c in range(2)) for f in FUN for g in FUN]

def cond_report(p,k):
    perm=[k]+[m for m in range(3) if m!=k]; pp=np.transpose(p,perm+[3+m for m in perm])
    marg=pp.sum(axis=(1,2))   # a,x,y,z
    mf=np.allclose(marg,marg[:, :1,:1,:1].repeat(2,1).repeat(2,2).repeat(2,3)) and np.allclose(marg,marg[:,0:1,0:1,0:1])
    if not mf: return dict(marg_first=False)
    sums=set()
    for a in range(2):
        pa=marg[a,0,0,0]
        if pa==0: continue
        for x in range(2): sums|=set(np.round(valid2(pp[a,:,:,x]/pa),12))
    return dict(marg_first=True,cond_sums=sorted(sums),cond_valid=sums=={1.0})

lug=lambda o:((1-o[1])*o[2],(1-o[2])*o[0],(1-o[0])*o[1])
h5=[(lambda be,ga:(lambda o:((be+ga+o[1]+o[2])%2,be,ga)))(be,ga) for be in range(2) for ga in range(2)]
for name,pfs,wts in [("Lugano",[lug],[1.0]),("H5",h5,[.25]*4)]:
    V=lift(pfs); J=len(pfs); p=classical(pfs,wts)
    for k in range(3):
        print(name,"party",k,"opfirst_resid=%.3g"%opfirst(V,k,J),"open_purity=%.2g"%open_purity(V,k,J),cond_report(p,k))
