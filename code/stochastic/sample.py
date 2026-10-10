import numpy as np, itertools as it, json
from scipy.optimize import linprog
B=list(it.product((0,1),repeat=3))
fs=list(it.product((0,1),repeat=2)); rows=[]
for f in it.product(fs,repeat=3):
    r=np.zeros((8,8))
    for x in B: r[B.index(x),B.index(tuple(f[k][x[k]] for k in range(3)))]+=1
    rows.append(r.ravel())
A=np.array(rows)
# symmetry group: party perm, flip input bit, flip output bit per party
def act(E,perm,fx,fa):
    F=np.zeros((8,8))
    for x in B:
        for a in B:
            x2=tuple(x[perm[k]]^fx[k] for k in range(3)); a2=tuple(a[perm[k]]^fa[k] for k in range(3))
            F[B.index(x2),B.index(a2)]=E[B.index(x),B.index(a)]
    return F
G=[(p,fx,fa) for p in it.permutations(range(3)) for fx in B for fa in B]
def canon(E):
    return min(tuple(np.round(act(E,*g),6).ravel()) for g in G)
rng=np.random.default_rng(0); reps={}; ndet=0; N=40000
for t in range(N):
    c=rng.normal(size=64)
    res=linprog(c,A_eq=A,b_eq=np.ones(len(A)),bounds=(0,None),method='highs-ds')
    E=res.x.reshape(8,8)
    if np.allclose(E,np.round(E),atol=1e-7): ndet+=1; continue
    k=canon(E)
    reps.setdefault(k,0); reps[k]+=1
print('samples',N,'deterministic',ndet,'nondet orbits',len(reps))
json.dump([[list(k),v] for k,v in reps.items()],open('reps.json','w'))
