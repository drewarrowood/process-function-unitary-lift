"""Round 20 (H.27.1, side check): do Lugano-wired no-signalling boxes p(i|o) = P(i|lug_sigma(o)) violate ANY facet of the PF hull?
Vectorised over all 29,344 facets: min over NS of each facet = min over the NS polytope's vertices is not available, so we solve one
LP per (facet, Lugano variant) with HiGHS [NUMERICAL]."""
import json, time
from scipy.optimize import linprog
from h20_common import *
from h20_fwd_ns import lug, wmap, Aeq, beq
t0=time.time(); worst=[]; nf=Tn.shape[0]
Cs=[]
for parts in lug:
    wm=wmap(parts); M=np.zeros((64,64))   # M[8*i+x, 8*i+o]
    for o in range(8):
        x=B3.index(wm[o])
        for i in range(8): M[8*i+x,8*i+o]=1
    Cs.append(M)
neg=0; mins=np.zeros((nf,8))
for f in range(nf):
    for v,M in enumerate(Cs):
        r=linprog(M@Tn[f,:64],A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs'); mins[f,v]=r.fun+Tn[f,64]
    if mins[f].min()<-1e-9: neg+=1
    if f%2000==0: print(f,'facets done; facets with a negative NS value so far:',neg,f'{time.time()-t0:.0f} s',flush=True)
np.save('h20_fwd_ns_all_mins.npy',mins)
m=mins.min(1); print('SUMMARY facets',nf,'with min < -1e-9:',int((m<-1e-9).sum()),' overall min',m.min(),' orbits of violated facets:',sorted(set(canon[m<-1e-9].tolist())),f'{time.time()-t0:.0f} s')
