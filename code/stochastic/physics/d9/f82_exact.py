# Exact (rational) facet-82 orbit violations for E_ex1 and the 51 sampled vertex orbits (D.9).
import json, itertools as it
from fractions import Fraction as Fr
B3=list(it.product((0,1),repeat=3)); idx={b:k for k,b in enumerate(B3)}
F82=[(+1,'000','000'),(-1,'000','001'),(-1,'010','001'),(-1,'000','100'),(-1,'010','110'),(-1,'011','111')]
F82=[(s,tuple(map(int,i)),tuple(map(int,o))) for s,i,o in F82]
def members():
    out=set()
    for pi in it.permutations(range(3)):
        for fi in B3:
            for fo in B3:
                g=lambda v,f:tuple(v[pi[k]]^f[k] for k in range(3))
                out.add(frozenset((s,g(i,fi),g(o,fo)) for s,i,o in F82))
    return out
M=members()
def val(p,m): return sum(s*p[idx[i]][idx[o]] for s,i,o in m)
def tomat(v): return [[Fr(v[8*a+b]).limit_denominator(64) for b in range(8)] for a in range(8)]
pfs=None
reps=json.load(open('reps.json'))
C=lambda o:(o[2],o[0],o[1])
Eex1=[[Fr(0)]*8 for _ in range(8)]
for o in B3:
    Eex1[idx[C(o)]][idx[o]]+=Fr(1,2); Eex1[idx[tuple(1-x for x in C(o))]][idx[o]]+=Fr(1,2)
res={'n_members':len(M)}
def stats(p):
    vs=[val(p,m) for m in M]; return max(vs), sum(1 for v in vs if v>0)
# orientation check: columns (fixed o) must sum to 1
r=[]
for k,(v,_) in enumerate(reps):
    p=tomat(v); colsum=[sum(p[a][b] for a in range(8)) for b in range(8)]
    if any(c!=1 for c in colsum): p=[list(x) for x in zip(*p)]
    mx,n=stats(p); r.append((k,str(mx),n))
mx,n=stats(Eex1)
print('members',len(M),'E_ex1',mx,n)
for x in r: print(*x)
print('all violated:',all(Fr(x[1])>0 for x in r))
import numpy as np
P=np.load('pfs.npy').astype(int)
worst=max(val(P[j].tolist(),m) for j in range(len(P)) for m in M)
tight=[sum(1 for j in range(len(P)) if val(P[j].tolist(),m)==0) for m in list(M)[:3]]
print('PFs',len(P),'max facet value over PFs and members',worst,'tight PFs (3 members)',tight)
