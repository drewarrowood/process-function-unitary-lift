"""Round 19 audit of the glue_k4 completeness claim (H.17.17, H.26.1).  Independent of glue_k4.py's bookkeeping:
(1) glue_k4_tuples.json (output of glue_k4enum.py) lists N labelled four-class geometries; the 'g' index used by glue_k4.py and in
    glue_k4_done.jsonl is the RAW position in this list (glue_k4.items()), not an orbit id.
(2) Recompute, for every one of the N geometries, its orbit key under cube translations x G48 (code re-written here, using only
    the group G, cls_act and pbits of t3sym), and check that glue_k4_canon.json contains exactly one geometry from every orbit
    (and nothing else).
(3) Check that every geometry in the canonical set has a record in glue_k4_done.jsonl, that every record of it has cand == [] and
    unres == 0, and report the job total; also report the raw coverage of done.jsonl (records from the pre-canonical first run).
Running the search on one geometry per orbit suffices because the symmetries are PROVED (H.17.15(d))."""
import json, collections
from t3sym import G, cls_act, pbits
T=json.load(open('glue_k4_tuples.json')); N=len(T)
import ast
def lab_of(t):
    pr=ast.literal_eval(t['geo'][0]); cid={v:i for i,p in enumerate(pr) for v in p}
    order=[cid[0]]+[i for i in range(4) if i!=cid[0]]
    L={order[j]:tuple(t['cls'][j]) for j in range(4)}
    return [(L[cid[v]],cid[v]) for v in range(8)]
def orbit_key(lab):
    best=None
    for g in G:
        pi=g[0]
        acted=[None]*8
        for v in range(8):
            L,c=lab[v]; acted[pbits(v,pi)]=(cls_act(g,L) if L else (),c)
        for t in range(8):
            ren={}; tup=[]
            for w in range(8):
                L,c=acted[w^t]; ren.setdefault(c,len(ren)); tup.append((L,ren[c]))
            tup=tuple(tup)
            if best is None or tup<best: best=tup
    return best
print('labelled geometries in glue_k4_tuples.json:',N,' distinct (cls,geo) entries:',len({json.dumps(t,sort_keys=True) for t in T}),flush=True)
orb=collections.defaultdict(list)
for gi,t in enumerate(T):
    orb[orbit_key(lab_of(t))].append(gi)
    if gi%5000==0: print(' keyed',gi,flush=True)
canon=json.load(open('glue_k4_canon.json')); cs=set(canon)
print('orbits under translations x G48:',len(orb),'; glue_k4_canon.json entries:',len(canon),'distinct',len(cs))
per=[sum(1 for g in m if g in cs) for m in orb.values()]
print('orbits with exactly one canonical representative:',sum(1 for x in per if x==1),'; with none:',sum(1 for x in per if x==0),'; with more than one:',sum(1 for x in per if x>1))
print('canonical entries outside range:',sum(1 for g in cs if not 0<=g<N))
recs=collections.defaultdict(list)
for l in open('glue_k4_done.jsonl'):
    r=json.loads(l); recs[r['g']].append(r)
print('done.jsonl: records',sum(len(v) for v in recs.values()),'; distinct raw indices',len(recs),'; range',min(recs),'..',max(recs))
missing=[g for g in canon if g not in recs]
bad=[g for g in canon if g in recs and any(r['cand'] or r['unres'] for r in recs[g])]
badall=[g for g in recs if any(r['cand'] or r['unres'] for r in recs[g])]
print('canonical geometries with a done record:',len(canon)-len(missing),'/',len(canon),'; missing:',missing[:20])
print('canonical geometries with a candidate or UNRESOLVED job:',len(bad),'; any record in done.jsonl with cand/unres:',len(badall))
print('jobs over canonical geometries (first record each):',sum(recs[g][0]['jobs'] for g in canon if g in recs))
print('non-canonical raw indices in done.jsonl (from the pre-canonical first run):',len([g for g in recs if g not in cs]))
orbits_hit=sum(1 for m in orb.values() if any(g in recs for g in m)); print('orbits with at least one done geometry (any index):',orbits_hit,'/',len(orb))
print('AUDIT', 'COMPLETE' if not missing and not bad and all(x==1 for x in per) else 'INCOMPLETE')
