"""Reduce Z_N X-type boards modulo output flips, party permutations, complex conjugation (re-gauged)."""
import numpy as np, itertools as it, sys
N=int(sys.argv[1]); M=np.load('xboards_z%d_full.npy'%N).astype(np.int16)
B3=list(it.product((0,1),repeat=3)); idx={t:i for i,t in enumerate(B3)}
reps=[];labs=[]
def canon(Mx):
    best=None
    for perm in it.permutations(range(3)):
        pz=[idx[tuple(t[perm[j]] for j in range(3))] for t in B3]
        for fl in it.product((0,1),repeat=3):
            po=[idx[tuple(t[perm[j]]^fl[j] for j in range(3))] for t in B3]
            for s in (1,-1):
                X=(s*Mx[:,po][:,:,pz])%N; X=(X-X[:,0:1,:])%N; X=(X-X[:,:,0:1])%N
                K=np.ascontiguousarray(X.reshape(len(X),64).astype(np.uint8)).view('S64')[:,0]
                best=K if best is None else np.where(K<best,K,best)
    return best
allk=[]
for ch in np.array_split(M,max(1,len(M)//20000)): allk.append(canon(ch))
allk=np.concatenate(allk); u,first,lab=np.unique(allk,return_index=True,return_inverse=True)
print('N',N,'boards',len(M),'classes',len(u))
np.save('xreps_z%d.npy'%N,M[first].astype(np.uint8))
