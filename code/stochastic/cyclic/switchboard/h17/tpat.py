"""Cancellation patterns of W = V'V^dag for two genuine 3-term classes V=a+i(bA+cB), V'=a'+i(b'A'+c'B') (all coefficients nonzero).
Step 1: coincidence structure of the 9 products {1,A',B'}x{1,A,B} over all pairs of anticommuting generator pairs."""
import numpy as np, itertools as it, collections, json
from lib3 import *
P3=[(a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
def ph(s,t):   # HM[s]@HM[t] = ph * HM[s^t]
    M=HM[s]@HM[t]; R=HM[s^t]; j=np.unravel_index(np.argmax(np.abs(R)),R.shape); return complex(np.round(M[j]/R[j]))
cnt=collections.Counter(); rep={}
for (A,B) in P3:
    for (A2,B2) in P3:
        L=[0,A2,B2]; Rr=[0,A,B]
        prods=[u^v for u in L for v in Rr]
        K={0,A,B,A^B}; K2={0,A2,B2,A2^B2}
        key=(len(K&K2), tuple(sorted(collections.Counter(prods).values(),reverse=True)))
        cnt[key]+=1; rep.setdefault(key,(A,B,A2,B2))
for k,v in sorted(cnt.items()): print(k,v,rep[k])
json.dump({str(k):rep[k] for k in rep},open('tpat_reps.json','w'))
