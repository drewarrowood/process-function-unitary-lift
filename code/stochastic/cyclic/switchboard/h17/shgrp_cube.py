"""H.17.9c [EXHAUSTIVE, EXACT, over-approximation]: every pairwise SH_grp failure (different classes c at o, c' at q, any D)
vs. the necessary CUBE edge conditions.  WLOG o=0, q=D.  Each other vertex gets a label in {c, c', n}, where n = a fresh
identity class V=1 (the most permissive new class) and sign variants are merged with their class (also permissive).  Each cube
edge (u, u xor e_p) whose endpoints have different labels needs all generators of both labels trivial on party p.
If no labelling exists, the failing pair cannot occur in any admissible cube.  The test depends only on the triviality
patterns TR[c], TR[c'] (3 bits each), so it is tabulated for all 64 pattern pairs and D.
Survivors (to be settled by an exact cube DFS) are written to shgrp_cube_survivors.json [resumable checkpoint]."""
import numpy as np, json, itertools as it, time
exec(open('shgrp_local.py').read().split('\nt0=time.time(); tot')[0])
def feasible(tc,tq,D):
    lab_tr={'c':tc,'q':tq,'n':(True,True,True)}
    others=[v for v in range(8) if v not in (0,D)]
    for L in it.product('cqn',repeat=6):
        lab=dict(zip(others,L)); lab[0]='c'; lab[D]='q'
        if all(lab[u]==lab[u^(1<<p)] or (lab_tr[lab[u]][p] and lab_tr[lab[u^(1<<p)]][p]) for u in range(8) for p in range(3)):
            return True
    return False
pats=list(it.product((False,True),repeat=3))
FE={(a,b,D):feasible(a,b,D) for a in pats for b in pats for D in range(1,8)}
SURV=[]
t0=time.time(); res={d:[0,0] for d in range(1,8)}
for i,c in enumerate(CL):
    M=(T[i][:,None,None]^T[None,:,:]).transpose(1,0,2).reshape(N,9)
    S=R[None,:,None]^M[:,None,:]
    adm=~FB[:,S].any(-1)
    X=(xR[None,:,None,None]^HH[i][None,None,:,None]^HH[:,None,None,:])
    bad=(((X[None]&Ds[:,None,None,None,None])==Ds[:,None,None,None,None]).any((-1,-2)))
    f=adm&bad; cnt=f.sum(-1)        # (7,N)
    for d in range(1,8):
        ok=np.array([FE[(tuple(TR[i]),tuple(TR[j]),d)] for j in range(N)])
        res[d][0]+=int(cnt[d-1].sum()); res[d][1]+=int(cnt[d-1][ok].sum())
        for j in np.nonzero(ok&(cnt[d-1]>0))[0]:
            for r in np.nonzero(f[d-1,j])[0]: SURV.append([list(c),list(CL[j]),int(r),d])
out=dict(per_D={d:dict(failures=a,cube_completable=b) for d,(a,b) in res.items()},
         total_failures=sum(a for a,b in res.values()),total_completable=sum(b for a,b in res.values()),secs=round(time.time()-t0)); json.dump(SURV,open('shgrp_cube_survivors.json','w'))
print(json.dumps(out,indent=1)); json.dump(out,open('shgrp_cube.json','w'),indent=1)
