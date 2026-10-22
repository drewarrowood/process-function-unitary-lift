"""Family A: source-sink lifts of single PFs (and phase variants); Family B: C.1 lifts of PF blends.
For a PF lift, I_k = w_k(o) + e_k, so party k is operator-first iff w_k is constant (checked numerically
with common.opfirst). Classical process = the PF itself (in the hull)."""
import numpy as np, itertools as it, json
from common import *
P=np.load('pfs744.npy'); rng=np.random.default_rng(1)
def wfun(Pm): return {o:B3[int(np.argmax(Pm[:,IX[o]]))] for o in B3}
def lift(ws,amps,phase=None):
    J=len(ws); V=np.zeros((8,J*8,8,J*8),complex)  # i, f=(j,o), o, s=(j,e)
    for j,w in enumerate(ws):
        for o in B3:
            for e in B3:
                i=tuple(a^b for a,b in zip(w[o],e)); ph=1 if phase is None else np.exp(1j*phase[j,IX[o],IX[e]])
                V[IX[i],j*8+IX[o],IX[o],j*8+IX[e]]=ph
    return V
def deps(w):  # does w_k depend on outputs at all
    return [len({w[o][k] for o in B3})>1 for k in range(3)]
nofirst=[n for n in range(len(P)) if all(deps(wfun(P[n])))]
# orbit structure of the no-first PFs under party perms and bit flips
def canon(Pm):
    best=None
    for pm in it.permutations(range(3)):
        for fi in it.product((0,1),repeat=3):
            for fo in it.product((0,1),repeat=3):
                Q=np.zeros((8,8))
                for i in B3:
                    for o in B3:
                        if Pm[IX[i],IX[o]]:
                            i2=tuple(i[pm[k]]^fi[k] for k in range(3)); o2=tuple(o[pm[k]]^fo[k] for k in range(3)); Q[IX[i2],IX[o2]]=1
                k=Q.tobytes(); best=k if best is None or k<best else best
    return best
orbs={}
for n in nofirst: orbs.setdefault(canon(P[n]),[]).append(n)
lug=[n for n in nofirst if wfun(P[n])[(0,0,1)]==(1,0,0) and wfun(P[n])[(1,0,0)]==(0,1,0) and wfun(P[n])[(0,1,0)]==(0,0,1) and wfun(P[n])[(0,0,0)]==(0,0,0) and wfun(P[n])[(1,1,1)]==(0,0,0)]
res=dict(n_pf=len(P),n_nofirst=len(nofirst),orbits=[])
for k,v in orbs.items():
    n=v[0]; w=wfun(P[n]); V=lift([w],[1]); r=opfirst(V,8)
    # random phase variant
    Vp=lift([w],[1],rng.uniform(0,2*np.pi,(1,8,8))); rp=opfirst(Vp,8)
    res['orbits'].append(dict(size=len(v),rep=n,w={''.join(map(str,o)):''.join(map(str,w[o])) for o in B3},opfirst=r,opfirst_phase=rp,
                             contains_lugano=any(m in v for m in lug)))
# Family B: blend of three causally ordered PFs whose first parties are A, B, C respectively
first=[[n for n in range(len(P)) if deps(wfun(P[n]))==d and sum(deps(wfun(P[n])))==2] for d in ([False,True,True],[True,False,True],[True,True,False])]
ws=[wfun(P[first[k][0]]) for k in range(3)]
VB=lift(ws,[1,1,1]); res['familyB']=dict(pfs=[first[k][0] for k in range(3)],opfirst=opfirst(VB,24))
print(json.dumps(res,indent=1))
json.dump(res,open('famA.json','w'),indent=1)
