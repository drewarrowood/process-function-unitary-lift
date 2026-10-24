"""Exact classification of cancellation patterns of W = V'V^dag, V=a+i(bA+cB), V'=a'+i(b'A'+c'B'), all coefficients nonzero.
Each product HM[u']HM[u] = ph*HM[u'^u]; coefficient of string s is sum over colliding (u',u) of ph * x'_{u'} * conj(x_u),
x=(a, i b, i c).  A collided string with two contributions t1 x'_{u'} x_u + t2 x'_{w'} x_w (x real up to the i's) can vanish
iff the two total phases are real multiples of each other; then the condition is one real bilinear equation.
We record, per pair, which subsets of collided strings can be killed simultaneously with all six coefficients nonzero
(checked by explicit construction: solve the equations for a random point and verify)."""
import numpy as np, itertools as it, collections, json
from lib3 import *
P3=[(a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
def ph(s,t):
    M=HM[s]@HM[t]; R=HM[s^t]; j=np.unravel_index(np.argmax(np.abs(R)),R.shape); return complex(np.round(M[j]/R[j],12))
rng=np.random.default_rng(1)
def W_of(v2,v,g2,g):
    V=v[0]*np.eye(8)+1j*(v[1]*HM[g[0]]+v[2]*HM[g[1]]); V2=v2[0]*np.eye(8)+1j*(v2[1]*HM[g2[0]]+v2[2]*HM[g2[1]])
    return V2@V.conj().T
def kill(g2,g,S,coll):
    """find unit v,v2 with all comps |.|>0.1 such that coefficients of strings in S vanish; None if not found"""
    from scipy.optimize import least_squares
    for _ in range(30):
        x0=rng.normal(size=6)
        f=lambda x: np.r_[[ (lambda c:[c.real,c.imag])(pauli_coeffs(W_of(x[3:]/np.linalg.norm(x[3:]),x[:3]/np.linalg.norm(x[:3]),g2,g))[s]) for s in S]].ravel()
        r=least_squares(f,x0,xtol=1e-15,ftol=1e-15,gtol=1e-15)
        v=r.x[:3]/np.linalg.norm(r.x[:3]); v2=r.x[3:]/np.linalg.norm(r.x[3:])
        if np.abs(f(r.x)).max()<1e-12 and min(np.abs(v).min(),np.abs(v2).min())>0.05:
            c=pauli_coeffs(W_of(v2,v,g2,g)); return sorted(int(s) for s in range(64) if abs(c[s])>1e-9)
    return None
types=collections.defaultdict(list)
for (A,B) in P3:
    for (A2,B2) in P3:
        K={0,A,B,A^B}; K2={0,A2,B2,A2^B2}
        if len(K&K2)==1: continue
        prods=collections.Counter(u^v for u in [0,A2,B2] for v in [0,A,B])
        coll=sorted(s for s in prods if prods[s]>1)
        types[(len(K&K2),)].append((A,B,A2,B2,coll))
res={}
for t,L in types.items():
    pats=collections.Counter()
    for (A,B,A2,B2,coll) in L[:60]:          # pattern per instance (structure is uniform under Clifford symmetry; sample 60)
        gen=sorted(set(u^v for u in [0,A2,B2] for v in [0,A,B]))
        for m in range(1,len(coll)+1):
            for S in it.combinations(coll,m):
                sup=kill((A2,B2),(A,B),S,coll)
                if sup is not None:
                    # describe the killed set by position in the generic support relative to K
                    pats[(len(gen),len(sup),tuple(sorted(len(set(gen)-set(sup)) for _ in [0])))]+=1
    res[str(t)]=dict(n=len(L),patterns={str(k):v for k,v in pats.items()})
    print(t,len(L),dict(pats),flush=True)
json.dump(res,open('tclass.json','w'),indent=1)
