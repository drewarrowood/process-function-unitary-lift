"""Rerun the UNRESOLVED jobs of tclose3g with a 100x node budget (and no budget if needed)."""
import gzip, json, time, tclose3g as T
rows=[json.loads(l.split('\t')[1]) for l in gzip.open('tclose3g_done.txt.gz','rt')]
U=[tuple(tuple(s) for s in j) for r in rows for j in r['unresolved']]
print('unresolved jobs', len(U))
for B in (20_000_000, 10**12):
    T.BUDGET=B; left=[]
    for j in U:
        t=time.time(); r=T.solve(j); print(B, j, r, '%.1fs'%(time.time()-t), flush=True)
        if r=='UNRESOLVED': left.append(j)
    U=left
    if not U: break
print('SUMMARY remaining unresolved', len(U))
