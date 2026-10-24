"""For each tuned board: are the nsearch classes equal up to sign (V'=+-V, a 'fake' tuning) and what is supp(V'V^dag)?"""
import json,glob,numpy as np,collections
from lib3 import *
def supp(K): c=pauli_coeffs(K); return [s for s in range(64) if abs(c[s])>1e-9]
c=collections.Counter()
for f in sorted(glob.glob('tb_*.npz')):
    d=np.load(f); U=d['U']; P=d['P']; k=d['k']; Vs={}
    for o in range(8): Vs.setdefault(int(k[o]),PM[P[o]].conj().T@U[o])
    ks=sorted(Vs); pairs=[]
    for i in range(len(ks)):
        for j in range(i+1,len(ks)):
            W=Vs[ks[j]]@Vs[ks[i]].conj().T; s=supp(W)
            pairs.append((len(supp(Vs[ks[i]])),len(supp(Vs[ks[j]])),len(s),len({px(x) for x in s})))
    c[tuple(pairs)]+=1
for k,v in c.items(): print(v,'  (|supp V|,|supp V2|,|supp V2 V^dag|,#X-parts):',k)
