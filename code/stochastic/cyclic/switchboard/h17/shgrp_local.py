"""H.17.9b [EXHAUSTIVE, EXACT, over-approximation]: which pairwise SH_grp failures (different classes c,c', |D|=2) survive
a necessary local completion test through a common neighbour m (edges o-m across party j, m-q across party k, {j,k}=D).
Across a cube edge of party p every term of K must be trivial on p; for different classes this forces all generators of both
classes to be trivial on p (the identity term forces R trivial on p, then each generator).  Options for m: same class+sign as o,
sign variant of o's class, same as q, sign variant of q's class, or a new class (gens trivial on both edge parties).
Over-approximation: R-decomposition always possible; only the class conditions are tested.  'infeasible' is a proof."""
import numpy as np, json, time
from lib3 import FORB, anti, px, pz
exec(open('shgrp_exh.py').read().split('t0=time.time()')[0])
def triv(c,p): return all((((px(g)|pz(g))>>p)&1)==0 for g in c[1:])
def flip_triv(c,p):  # some sign variant of c differs from c only by a generator trivial on p (S(ds) terms trivial on p)
    if c[0]==1: return False
    if c[0]==2: return triv(c,p)
    a,b=c[1],c[2]; t=lambda g:(((px(g)|pz(g))>>p)&1)==0
    return (t(a) and t(a^b)) or (t(b) and t(a^b)) or (t(a) and t(b))
TR=np.array([[triv(c,p) for p in range(3)] for c in CL]); FT=np.array([[flip_triv(c,p) for p in range(3)] for c in CL])
t0=time.time(); tot=0; surv=0; tot3=0; ex=[]
for i,c in enumerate(CL):
    M=(T[i][:,None,None]^T[None,:,:]).transpose(1,0,2).reshape(N,9)
    S=R[None,:,None]^M[:,None,:]
    adm=~FB[:,S].any(-1)
    X=(xR[None,:,None,None]^HH[i][None,None,:,None]^HH[:,None,None,:])
    bad=(((X[None]&Ds[:,None,None,None,None])==Ds[:,None,None,None,None]).any((-1,-2)))
    f=adm&bad
    for d in range(1,8):
        bits=[p for p in range(3) if (d>>p)&1]
        F=f[d-1].any(1)            # class pairs (c, c') failing for some R
        if len(bits)==3: tot3+=int(f[d-1].sum()); continue
        if len(bits)!=2: continue
        cnt=f[d-1].sum(1); tot+=int(cnt.sum())
        ok=np.zeros(N,bool)
        for (j,k) in [(bits[0],bits[1]),(bits[1],bits[0])]:   # m = o xor e_j: edge o-m party j, edge m-q party k
            ci=TR[i]; cf=FT[i]
            both_k=TR[i][k]&TR[:,k]; both_j=TR[i][j]&TR[:,j]
            ok|= both_k                                   # m ~ o (exact)
            ok|= both_j                                   # m ~ q (exact)
            ok|= (TR[i][j] & TR[:,k])                     # m new class (gens trivial on j and k) or variants (implied)
        s=int(cnt[ok].sum()); surv+=s
        if s and len(ex)<10:
            j2=np.nonzero(ok&F)[0][:2]; ex+= [(c,CL[x],d) for x in j2]
out=dict(D2_failures=tot,D2_locally_completable=surv,D3_failures=tot3,examples=[str(e) for e in ex[:10]],secs=round(time.time()-t0))
print(json.dumps(out,indent=1)); json.dump(out,open('shgrp_local.json','w'),indent=1)
