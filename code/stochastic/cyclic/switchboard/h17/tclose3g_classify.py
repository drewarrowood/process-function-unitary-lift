"""H.17.15 closing step: classify the 188 candidates and 1,274 UNRESOLVED jobs of the finished tclose3g run by orbit and by
which triple-consistency inclusion they violate (tclose3g_cand.py); control: fraction of ALL jobs that are triple-consistent
(so the filter is not vacuous), and the supports of the two known three-class tuned boards."""
import gzip, json, collections, sys
from tclose3g_cand import consistent, sums
rows=[(int(l.split('\t')[0]),json.loads(l.split('\t')[1])) for l in gzip.open('tclose3g_done.txt.gz','rt')]
tot=collections.Counter(); kinds=collections.Counter(); per=[]
def kind(j):
    ab,ac,bc=map(set,j); mono=[len(s)==1 for s in (ab,ac,bc)]
    fails=[n for n,(x,y,z) in (('ac',(ac,ab,bc)),('ab',(ab,ac,bc)),('bc',(bc,ab,ac))) if not x<=sums(y,z)]
    return ('monomial pattern '+''.join('M' if m else 'n' for m in mono)), tuple(fails)
for ai,d in rows:
    nc,nu=len(d['cand']),len(d['unresolved'])
    for j,r in d['cand']: kinds[('cand',)+kind(j)]+=1; assert not consistent(j)
    for j in d['unresolved']: kinds[('unres',)+kind(j)]+=1; assert not consistent(j)
    per.append((ai,tuple(d['rep']),d['jobs'],nc,nu))
print('per orbit (orbit, rep, jobs, cand, unresolved) -- all cand/unres triple-inconsistent:')
for p in per: print(' ',p)
print('orbits with cand>0:',sum(1 for p in per if p[3]),' with unres>0:',sum(1 for p in per if p[4]),' clean (0/0):',sum(1 for p in per if not p[3] and not p[4]))
print('kinds (type, which of S_ab,S_ac,S_bc are single strings, violated inclusions):')
for k,v in sorted(kinds.items()): print(' ',k,v)
print('known tuned boards supports ((0,4,32,36),(4,),(0,4,32,36)) consistent:',consistent(((0,4,32,36),(4,),(0,4,32,36))))
if 'ctrl' in sys.argv:
    import tclose3g as T
    for ai in (0,9,30):
        J=T.gen_jobs(ai); c=sum(consistent(j) for j in J); print(f'control orbit {ai}: {c} of {len(J)} jobs triple-consistent',flush=True)
