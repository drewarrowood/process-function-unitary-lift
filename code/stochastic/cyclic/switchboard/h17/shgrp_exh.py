"""H.17.9 [EXHAUSTIVE, EXACT; generic-support model]: pairwise SH_grp.
For every ordered pair of class options (type 1: V=1; type 2: generator A; type 3: anticommuting A<B), including two
distinct classes with identical generators, every R = P_o xor P_q (64) and every D != 0 (7):
  generic support of K = R + {0,A,B} + {0,A',B'} (different classes)  or  R + S(ds) (sign variants of one class, ds != 0);
  if this support avoids all forbidden strings for D (pairwise admissible), check SH_grp:
  every X-string x(R) + h + h' (h in H_k = <x-parts of gens of k>, h' in H_k') satisfies (x & D) != D.
Pairwise SH_grp on every admissible pair => SH_grp on every admissible cube => PF blend (H.17.8)."""
import numpy as np, itertools as it, json, time
from lib3 import FORB, anti, px
CL=[(1,)]+[(2,a) for a in range(1,64)]+[(3,a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
def terms(c): return [0]+list(c[1:])
def H(c):
    G={0}
    for g in c[1:]: G|={h^px(g) for h in G}
    return sorted(G)
N=len(CL); T=np.array([(terms(c)+[0,0])[:3] for c in CL]); HH=np.array([(H(c)*4)[:4] for c in CL])
R=np.arange(64); xR=R&7
FB=FORB[1:]                      # (7,64)  D=1..7
Ds=np.arange(1,8)
t0=time.time(); n_adm=0; fails=[]; n_fail=0
for i,c in enumerate(CL):
    M=(T[i][:,None,None]^T[None,:,:]).transpose(1,0,2).reshape(N,9)        # (N,9) term products
    S=R[None,:,None]^M[:,None,:]                                          # (N,64,9)
    adm=~FB[:,S].any(-1)                                                  # (7,N,64)
    X=(xR[None,:,None,None]^HH[i][None,None,:,None]^HH[:,None,None,:])    # (N,64,4,4)
    bad=(((X[None]&Ds[:,None,None,None,None])==Ds[:,None,None,None,None]).any((-1,-2)))  # (7,N,64)
    f=adm&bad; n_adm+=int(adm.sum()); k=int(f.sum()); n_fail+=k
    if k and len(fails)<20:
        for d,j,r in zip(*np.nonzero(f)): fails.append((c,CL[j],int(r),int(d+1)));
# sign variants of one type-3 class (ds=1,2,3) and type-2 class (ds=1)
sv_adm=0; sv_fail=0; svex=[]
for c in CL:
    if c[0]==1: continue
    a=c[1]; b=c[2] if c[0]==3 else None
    for ds in ([1] if c[0]==2 else [1,2,3]):
        Sset=[0,a] if c[0]==2 else {1:[0,a,a^b],2:[0,b,a^b],3:[0,a,b]}[ds]
        h=H(c)
        for r in range(64):
            for D in range(1,8):
                if any(FORB[D][r^s] for s in Sset): continue
                sv_adm+=1
                if any(((px(r)^u^v)&D)==D for u in h for v in h):
                    sv_fail+=1
                    if len(svex)<10: svex.append((c,ds,r,D))
out=dict(classes=N,diff_class_admissible=n_adm,diff_class_SHgrp_fail=n_fail,examples=[str(x) for x in fails[:20]],
         signvariant_admissible=sv_adm,signvariant_SHgrp_fail=sv_fail,sv_examples=[str(x) for x in svex],secs=round(time.time()-t0))
print(json.dumps(out,indent=1)); json.dump(out,open('shgrp_exh.json','w'),indent=1)
