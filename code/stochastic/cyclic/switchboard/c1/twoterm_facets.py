"""For every admissible two-term board (twoterm_pairs.json) and t in a grid, lambda_max of F_m(t) over the 384
members of facet orbit 82 (bound 0). lambda_max>0 would give a source state phi whose statistics leave the hull."""
import json, itertools as it, numpy as np, sys
B3=list(it.product((0,1),repeat=3)); IX={b:n for n,b in enumerate(B3)}
F82=[(+1,'000','000'),(-1,'000','001'),(-1,'010','001'),(-1,'000','100'),(-1,'010','110'),(-1,'011','111')]
F82=[(s,tuple(map(int,i)),tuple(map(int,o))) for s,i,o in F82]
mem=set()
for pi in it.permutations(range(3)):
    for fi in B3:
        for fo in B3:
            g=lambda v,f:tuple(v[pi[k]]^f[k] for k in range(3))
            mem.add(frozenset((s,IX[g(i,fi)],IX[g(o,fo)]) for s,i,o in F82))
MEM=[sorted(m) for m in mem]
P=np.array(json.load(open('twoterm_pairs.json')))   # (n,2,8)
P=P[P[:,0].tolist()!=P[:,1].tolist()] if False else P[[not np.array_equal(a,b) for a,b in P]]
n=len(P); worst=-9; arg=None
for t in [np.pi/8,np.pi/4,3*np.pi/8,np.pi/12,5*np.pi/12]:
    c,s=np.cos(t),np.sin(t)
    for m in MEM:
        F=np.zeros((n,8,8),complex)
        for sg,i,o in m:
            a=i^P[:,0,o]; b=i^P[:,1,o]
            v=np.zeros((n,8),complex); v[np.arange(n),a]+=c; v[np.arange(n),b]+=-1j*s
            F+=sg*np.einsum('ni,nj->nij',v,v.conj())
        lm=np.linalg.eigvalsh(F)[:,-1]; k=int(lm.argmax())
        if lm[k]>worst: worst=float(lm[k]); arg=(t,m,P[k].tolist())
print('pairs',n,'max lambda_max over facet-82 members and t grid: %.3e'%worst); print(json.dumps(arg,default=str))
