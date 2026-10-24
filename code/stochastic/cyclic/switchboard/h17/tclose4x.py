"""H.17.16c (Track A3): cross-cluster k = 4 classes, SAMPLED [each sampled class 4-tuple is solved exhaustively and exactly;
the sample as a whole is NUMERICAL evidence, not a proof].  WLOG (H.17.15(d) symmetry + relabelling) class 0 is a G48 orbit
representative a (61), class 1 is a class b tuned with a (b != a), classes 2,3 are any two further classes (identity class
() allowed), all four distinct.  For each sampled tuple all support assignments passing filters A and C (tclose56.lazy_jobs)
are solved with tclose4.solve (same root/leaf tests as tclose3g/tclose4).  Sample list is a fixed function of the seed, so
the run is resumable: checkpoint tclose4x_<seed>.jsonl (one line per tuple index); rerun the same command to continue.
Also prints the size of the full tuple space for the cost estimate.  Usage: NPROC=2 nohup python3 tclose4x.py <seed> <N> &"""
import os, sys, json, random, time
from multiprocessing import Pool
import tclose4 as T4, tclose56 as T56
from tclose2 import classes
from t3sym import reps, tuned
def work(a):
    cls,sup=a; r=T4.solve(dict(cls=cls,sup=sup)); return (None if r is None else r), sup
if __name__=='__main__':
    seed=int(sys.argv[1]); N=int(sys.argv[2]); NP=int(os.environ.get('NPROC','2')); rng=random.Random(seed)
    allc=list(classes)                                       # 1,072 incl. identity
    tp={a:[b for b in classes[1:] if b!=a and tuned(a,b)] for a in reps}
    space=sum(len(tp[a])*(len(allc)-2)*(len(allc)-3)//2 for a in reps)
    print('tuple space (a rep, b tuned, {c,d}):',space,flush=True)
    sample=[]
    for i in range(N):
        a=rng.choice(reps); b=rng.choice(tp[a]); rest=[c for c in rng.sample(allc,4) if c not in (a,b)][:2]
        sample.append([a,b]+rest)
    CK='tclose4x_%d.jsonl'%seed; done=set()
    if os.path.exists(CK):
        for l in open(CK): done.add(json.loads(l)['i'])
    t0=time.time()
    with Pool(NP) as pool:
        for i,cls in enumerate(sample):
            if i in done: continue
            t1=time.time(); n=0; cand=[]; unr=0
            for r,sup in pool.imap_unordered(work,((cls,s) for s in T56.lazy_jobs(cls)),chunksize=64):
                n+=1
                if r=='UNRESOLVED': unr+=1
                elif r is not None: cand.append(dict(sup=sup,sol=r))
            with open(CK,'a') as f: f.write(json.dumps(dict(i=i,cls=cls,jobs=n,cand=cand,unres=unr,sec=round(time.time()-t1,2)))+'\n')
            if cand or unr: print('i',i,cls,'jobs',n,'CAND',len(cand),'UNRES',unr,flush=True)
            if i%25==0: print('i',i,'elapsed',round(time.time()-t0),flush=True)
    print('done',flush=True)
