"""Round 20: enumerate 'refined' process functions with binary outputs: w_k(o) = block of o_{-k} in a partition of the 4 values of
o_{-k}, such that EVERY binary colouring of the blocks is one of the 744 binary PFs.  These are exactly the PFs (binary outputs,
arbitrary input alphabets) up to relabelling of input values."""
import json, time
from h20_common import *
t0=time.time(); good=[]
for parts in it.product(PARTS,repeat=3):
    if is_refined_pf(parts): good.append(parts)
nb=lambda p:tuple(max(x)+1 for x in p)
import collections
print('refined PFs (partition triples):',len(good),' by block counts:',sorted(collections.Counter(nb(p) for p in good).items()),f'{time.time()-t0:.0f} s')
def coarser(p,q): # p is a coarsening of q (q refines p) for every party
    return all(all((q[k][a]==q[k][b])<=(p[k][a]==p[k][b]) for a in range(4) for b in range(4)) for k in range(3))
maxi=[p for p in good if not any(q!=p and coarser(p,q) for q in good)]
print('maximal (not a coarsening of another):',len(maxi),' by block counts:',sorted(collections.Counter(nb(p) for p in maxi).items()))
json.dump(dict(all=good,maximal=maxi),open('h20_fwd_enum.json','w'))
for p in maxi[:40]: print(p)
