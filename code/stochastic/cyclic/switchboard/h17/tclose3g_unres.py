"""Rerun the UNRESOLVED jobs of tclose3g (checkpoint tclose3g_done.txt.gz) with a 100x node budget, 8 cores.
Writes tclose3g_unres_done.txt.gz: one line per job (orbit, job, result); resumable."""
import gzip, json, os, time
from multiprocessing import Pool
import tclose3g as T
def run(x):
    ai,j=x; T.BUDGET=20_000_000; t=time.time(); r=T.solve(j); return ai,j,r,round(time.time()-t,1)
if __name__=='__main__':
    rows=[json.loads(l.split('\t')[1]) for l in gzip.open('tclose3g_done.txt.gz','rt')]
    idx=[int(l.split('\t')[0]) for l in gzip.open('tclose3g_done.txt.gz','rt')]
    CK='tclose3g_unres_done.txt.gz'; done=set()
    if os.path.exists(CK):
        for l in gzip.open(CK,'rt'): d=json.loads(l); done.add((d[0],json.dumps(d[1])))
    U=[(ai,[list(s) for s in j]) for ai,r in zip(idx,rows) for j in r['unresolved']]
    U=[(ai,tuple(tuple(s) for s in j)) for ai,j in U if (ai,json.dumps(j)) not in done]
    print('unresolved jobs to run',len(U),flush=True)
    with Pool(8) as pool:
        for ai,j,r,dt in pool.imap_unordered(run,U):
            with gzip.open(CK,'at') as fo: fo.write(json.dumps([ai,j,r])+'\n')
            print(ai,j,r,dt,flush=True)
    res=[json.loads(l) for l in gzip.open(CK,'rt')]
    print('SUMMARY rerun',len(res),'cand',sum(1 for x in res if x[2] not in (None,'UNRESOLVED')),'still unresolved',sum(1 for x in res if x[2]=='UNRESOLVED'),flush=True)
