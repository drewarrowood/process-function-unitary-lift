"""H.17.17 cross-check of Lemma H's corollary 'no board has five or more classes' [NUMERICAL, independent code path]:
the H.17.16 solver with the leaf loosened to 'all k classes present' (tclose4.solve(loosen=True)) on Klein-cluster jobs.
Lemma H predicts: boards found for k = 4 (control), none for k = 5."""
import itertools as it, random, time
import tclose4 as T4, tclose56 as T56
from t3sym import Kof
random.seed(5)
K=(1,8,9)   # K0 = {1, X1, Z1, Y1}: the six classes of its cluster
A,B,AB=1,8,9; six=[(A,),(B,),(AB,),(A,B),(A,AB),(B,AB)]
six=[tuple(sorted(c)) for c in six]
for k in (4,5):
    found=tot=0; t0=time.time()
    for sub in it.combinations(six,k):
        if not any(len(c)==2 for c in sub): continue
        jobs=list(T56.lazy_jobs(list(sub))); random.shuffle(jobs)
        for sup in jobs[:15]:
            r=T4.solve(dict(cls=list(sub),sup=sup),loosen=True); tot+=1; found+=(r not in (None,'UNRESOLVED'))
    print('k',k,'sampled jobs',tot,'boards with all k classes found',found,'(%ds)'%(time.time()-t0),flush=True)
