import json,numpy as np,collections
P=np.array(json.load(open('twoterm_pairs.json'))); P=P[[not np.array_equal(a,b) for a,b in P]]
d=P[:,0]^P[:,1]; const=(d==d[:,:1]).all(1); print('pairs',len(P),'constant w1^w2',int(const.sum()))
print('distinct values of w1^w2 among nonconstant',dict(collections.Counter(len(set(x)) for x in d[~const].tolist())))
rng=np.random.default_rng(0); idx=rng.choice(np.nonzero(~const)[0],500,replace=False); nc=0
c=s=2**-.5
for w1,w2 in P[idx]:
    V=np.zeros((64,8),complex)
    for o in range(8):
        for i in range(8): V[8*o+i,i^w1[o]]+=c; V[8*o+i,i^w2[o]]+=-1j*s
    G=V.conj()@V.T            # overlaps <v_a|v_b>; rank-1 projectors commute iff overlap is 0 or modulus 1
    a=np.abs(G); nc+= bool(((a>1e-9)&(a<1-1e-9)).any())
print('random nonconstant sample 500: non-commuting',nc)
