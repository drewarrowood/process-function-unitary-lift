import sys, glob, json, numpy as np
from common import *
from purity import purity_resid
P=list(np.load('pfs744.npy'))
def buildV(C):
    V=np.zeros((8,8,8,8,8,8),complex)
    for o in range(8):
        for e in range(8):
            for t in range(8): V[e,o,e^t,o,:,t]=C[o,e,:]
    return V.reshape(8,64,8,64)
out=[]
for f in sorted(glob.glob(sys.argv[1] if len(sys.argv)>1 else 'P_*.npy')):
    C=np.load(f)
    for k in range(8):
        u,_,vh=np.linalg.svd(C[k]); C[k]=u@vh
    V=buildV(C); p=(abs(C[:,:,0])**2).T
    r=dict(file=f,purity=purity_resid(V,6,2),purity_noanc=purity_resid(V,6,1),opfirst=opfirst(V,64),
           valid=valid(p),hull_dist=in_hull(p,P))
    out.append(r); print(json.dumps(r),flush=True)
json.dump(out,open(sys.argv[2] if len(sys.argv)>2 else 'analyzeC.json','w'),indent=1)
