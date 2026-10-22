"""For polished family-C purifications: causal graph (pairwise influence O_j -> I_k), operator-first residuals,
and the minimal Lugano-orbit weight needed in a PF decomposition of the induced p (LP). Weight 0 means p is a
blend of PFs that each have a first party, i.e. classically causally separable (H.2)."""
import sys, glob, json, numpy as np, scipy.optimize as so
from common import *
from purity import purity_resid
P=np.load('pfs744.npy')
def deps(Pm):
    w={o:B3[int(np.argmax(Pm[:,IX[o]]))] for o in B3}; return [len({w[o][k] for o in B3})>1 for k in range(3)]
lugmask=np.array([all(deps(Pm)) for Pm in P])
def buildV(C):
    V=np.zeros((8,8,8,8,8,8),complex)
    for o in range(8):
        for e in range(8):
            for t in range(8): V[e,o,e^t,o,:,t]=C[o,e,:]
    return V.reshape(8,64,8,64)
def min_lug_weight(p):
    A=np.array([Pm.ravel() for Pm in P]).T; n=len(P)
    r=so.linprog(lugmask.astype(float),A_eq=np.vstack([A,np.ones((1,n))]),b_eq=np.r_[p.ravel(),1],bounds=(0,None),method='highs')
    return r.fun if r.status==0 else None
def min_lug_weight_tol(p,tol=1e-8):
    # robust version: allow L1 slack tol
    A=np.array([Pm.ravel() for Pm in P]).T; n=len(P); m=A.shape[0]
    c=np.r_[lugmask.astype(float),np.zeros(2*m)]
    Aeq=np.block([[A,np.eye(m),-np.eye(m)],[np.ones((1,n)),np.zeros((1,2*m))]])
    Aub=np.r_[np.zeros(n),np.ones(2*m)][None]
    r=so.linprog(c,A_ub=Aub,b_ub=[tol],A_eq=Aeq,b_eq=np.r_[p.ravel(),1],bounds=(0,None),method='highs')
    return r.fun if r.status==0 else None
if __name__=='__main__':
    out=[]
    for f in sorted(glob.glob(sys.argv[1])):
        C=np.load(f); V=buildV(C); p=(abs(C[:,:,0])**2).T
        r=dict(file=f,purity=purity_resid(V,4,2),opfirst=opfirst(V,64),influence=influence(V,64),
               hull_dist=in_hull(p,P),min_lugano_weight=min_lug_weight_tol(p,1e-7))
        out.append(r); print(json.dumps(r),flush=True)
    json.dump(out,open(sys.argv[2],'w'),indent=1)
