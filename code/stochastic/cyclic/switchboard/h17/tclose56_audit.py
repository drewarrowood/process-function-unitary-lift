"""Audit of the finished tclose56.py k = 5 run (H.17.16b, H.27.4).  Independent of tclose56.py's block bookkeeping:
(1) re-enumerate all Klein groups K = {A, B, AB} of anticommuting three-qubit Pauli pairs and their G48 orbits
    (own orbit code, using only t3sym.G/act and tclose2.anti); check that tclose4.klein_reps() returns one per orbit;
(2) for each representative K, recompute the stabiliser Stab(K) and the Stab(K)-orbits of the 6 five-element class subsets of
    its cluster (own union-find, not tclose56.stab_subsets); the expected blocks are one per orbit, any member being sound;
(3) check tclose56_done.txt.gz: one record per expected block (matched by Stab-orbit, not by the chosen representative), no
    duplicates, no extra records, every record with cand == [] and n_unres == 0; job total;
(4) check that the log lines agree with the records and the SUMMARY line;
(5) recount the jobs of sample blocks with an independent eager generator (itertools.product over the deduplicated pattern
    lists, filters A and C applied afterwards), compared with the records."""
import gzip, json, itertools as it, re, sys, time
from t3sym import G, act
from tclose2 import anti
import tclose4 as T4
from tclose3 import patterns
def kact(K,g): return tuple(sorted(act(s,*g) for s in K))
Ks={tuple(sorted((A,B,A^B))) for A in range(1,64) for B in range(A+1,64) if anti(A,B)}
orbs={}
for K in Ks: orbs.setdefault(min(kact(K,g) for g in G),[]).append(K)
reps,nK=T4.klein_reps()
print('(1) Klein groups',len(Ks),'(tclose4: %d)'%nK,' G48-orbits',len(orbs),' tclose4 reps',len(reps),
      ' reps = orbit minima:',sorted(orbs)==sorted(reps),' orbit sizes sum',sum(len(v) for v in orbs.values()))
expected={}   # (ki, frozenset-of-orbit) -> orbit
for ki,K in enumerate(reps):
    cl=T4.cluster(K); idx={c:i for i,c in enumerate(cl)}
    stab=[]
    for g in G:
        img=[tuple(sorted(act(s,*g) for s in c)) for c in cl]
        if sorted(img)==sorted(cl): stab.append([idx[c] for c in img])
    subs=list(it.combinations(range(6),5)); par={s:s for s in subs}
    def find(s):
        while par[s]!=s: s=par[s]
        return s
    for p in stab:
        for s in subs:
            t=tuple(sorted(p[i] for i in s)); a,b=find(s),find(t)
            if a!=b: par[a]=b
    groups={}
    for s in subs: groups.setdefault(find(s),set()).add(s)
    for gset in groups.values(): expected[(ki,frozenset(gset))]=gset
print('(2) expected blocks (K-rep, Stab-orbit of 5-subsets):',len(expected))
recs=[json.loads(l) for l in gzip.open('tclose56_done.txt.gz','rt')]
blks=[json.dumps(r['blk']) for r in recs]
print('(3) records',len(recs),' distinct blk',len(set(blks)),' all k=5:',all(r['blk'][1]==5 for r in recs))
hit={}; extra=[]
for r in recs:
    ki,k,sub=r['blk']; key=[e for e in expected if e[0]==ki and tuple(sub) in e[1]]
    if len(key)!=1: extra.append(r['blk']); continue
    hit.setdefault(key[0],[]).append(r)
missing=[e for e in expected if e not in hit]; dup=[e for e in hit if len(hit[e])>1]
tot=sum(r['jobs'] for r in recs); cand=sum(len(r['cand']) for r in recs); unres=sum(r['n_unres'] for r in recs)
print('    covered',len(hit),' missing',len(missing),' duplicate orbits',len(dup),' extra',len(extra))
print('    jobs',tot,' candidates',cand,' unresolved',unres,' job sizes',sorted({r['jobs'] for r in recs}),
      ' blocks per size',{s:sum(1 for r in recs if r['jobs']==s) for s in sorted({r['jobs'] for r in recs})})
L=[l for l in open('tclose56.log') if re.match(r'k 5 K \d', l)]
lg={}
for l in L:
    m=re.match(r'k 5 K (\d+) \(.*?\) sub \(([\d, ]+)\) jobs (\d+) cand (\d+) unres (\d+)',l)
    lg[json.dumps([int(m[1]),5,[int(x) for x in m[2].split(',')]])]=(int(m[3]),int(m[4]),int(m[5]))
agree=all(lg.get(json.dumps(r['blk']))==(r['jobs'],len(r['cand']),r['n_unres']) for r in recs)
summ=[l for l in open('tclose56.log') if l.startswith('SUMMARY')]
print('(4) log block lines',len(L),' agree with records:',agree and len(lg)==len(recs),' SUMMARY:',summ[-1].strip() if summ else None,
      ' invocations (header lines):',sum(1 for l in open('tclose56.log') if l.startswith('k 5 Klein')))
def eager_count(cls):
    k=len(cls); prs=list(it.combinations(range(k),2))
    pl=[list(dict.fromkeys(frozenset(S) for S in patterns(cls[i],cls[j]) if len(S)!=1)) for i,j in prs]
    n=0
    for ch in it.product(*pl):
        sup=dict(zip(prs,ch)); ok=True
        for i,j,l in it.combinations(range(k),3):
            a,b,c=sup[(i,j)],sup[(i,l)],sup[(j,l)]
            if not (b<={x^y for x in a for y in c} and a<={x^y for x in b for y in c} and c<={x^y for x in a for y in b}): ok=False; break
        n+=ok
    return n, int(__import__('math').prod(len(p) for p in pl))
NS=int(sys.argv[1]) if len(sys.argv)>1 else 6
small=[r for r in recs if r['jobs']==8019]; big=[r for r in recs if r['jobs']!=8019]
if NS>=0: small,big=small[:NS],big[:1]   # NS < 0: recount all 104 blocks
mism=0
for r in small+big:
    t=time.time(); ki,k,sub=r['blk']; cl=T4.cluster(reps[ki]); n,P=eager_count([cl[i] for i in sub])
    print('(5) block',r['blk'],' eager product',P,' filtered',n,' record',r['jobs'],' match',n==r['jobs'],f'{time.time()-t:.0f}s',flush=True)
    mism+=(n!=r['jobs'])
ok=(len(orbs)==len(reps) and not missing and not dup and not extra and cand==0 and unres==0 and len(recs)==len(expected) and mism==0)
print('AUDIT', 'PASS' if ok else 'FAIL', ': expected blocks',len(expected),'records',len(recs),'jobs',tot,'cand',cand,'unres',unres,'| eager recount',len(small+big),'blocks, mismatches',mism)
