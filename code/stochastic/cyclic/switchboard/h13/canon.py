"""Reduce Z_4 X-type boards modulo: output flips, party permutations, complex conjugation (re-gauged)."""
import numpy as np, itertools as it
from xenum import D4, B3, W
b=np.load('xboards_z4.npy').astype(np.int64); M=D4[b]          # [N,o,z]
idx={t:i for i,t in enumerate(B3)}
def key(Mx):
    Mx=(Mx-Mx[:,0:1,:])%4; Mx=(Mx-Mx[:,:,0:1])%4
    return (Mx.reshape(len(Mx),-1)*1).astype(np.int8)
keys=[]
for perm in it.permutations(range(3)):
    pz=[idx[tuple(t[perm[j]] for j in range(3))] for t in B3]
    for fl in it.product((0,1),repeat=3):
        po=[idx[tuple(t[perm[j]]^fl[j] for j in range(3))] for t in B3]
        for s in (1,-1):
            keys.append(key((s*M[:,po][:,:,pz])%4))
K=np.stack(keys,1)                                              # [N,96,64]
V=np.ascontiguousarray(K).view(np.dtype((np.void,64)))[...,0]
c=np.sort(V,1)[:,0]; u,first,lab=np.unique(c,return_index=True,return_inverse=True)
print('boards',len(b),'classes',len(u))
np.save('xreps.npy',b[first].astype(np.uint16)); np.save('xlab.npy',lab.astype(np.int32))
