"""H.17.17(d): enumerate every LABELLED GEOMETRY a board with exactly four classes can have [exhaustive over labels].
By Lemma H every class occupies exactly two vertices; a non-identity class sits on one edge along a rigid direction.
Constraints used (all PROVED necessary): two vertices joined by an edge along q carry the same class, or classes whose
labels x, y admit a pattern S (|S| >= 2, Lemma A) of supp(V_x V_y^dag) that is q-constant (Lemma B); at most one class has
the identity label; vertex 0 carries a three-term class whose label is a G48-orbit representative (translation + G48).
Output: glue_k4_tuples.json = sorted list of distinct label 4-tuples (class 0 = the rep), with the geometries found."""
import itertools as it, pickle, json, collections
from tclose2 import classes
from t3sym import reps
N,rigid=pickle.load(open('/tmp/glue_adj.pkl','rb'))
V=range(8); E=[(v,v^(1<<q),q) for v in V for q in range(3) if v<v^(1<<q)]
pairings=[]
def gen(rest,acc):
    if not rest: pairings.append(acc); return
    a=rest[0]
    for b in rest[1:]: gen([x for x in rest if x not in (a,b)],acc+[(a,b)])
gen(list(V),[])
print('pairings of 8 vertices',len(pairings))
tuples=collections.defaultdict(set); ngeo=0
for pr in pairings:
    nonedge=[p for p in pr if bin(p[0]^p[1]).count('1')!=1]
    if len(nonedge)>1: continue
    cid={v:i for i,p in enumerate(pr) for v in p}
    i0=cid[0]
    if pr[i0] in nonedge: continue                     # class at 0 is three-term, so its pair is an edge
    # inter-class constraints: list of (i,j,q)
    cons=[(cid[u],cid[w],q) for u,w,q in E if cid[u]!=cid[w]]
    order=[i0]+[i for i in range(4) if i!=i0]
    for a in reps:
        if not N.get((a,0)) and not N.get((a,1)) and not N.get((a,2)): continue
        lab={i0:a}
        def ok(i):
            for x,y,q in cons:
                if x in lab and y in lab and (x==i or y==i):
                    if lab[y] not in N.get((lab[x],q),()): return False
            if list(lab.values()).count(())>1: return False
            j=[i for i in lab if pr[i] in nonedge]
            if j and lab[j[0]]!=(): return False        # a non-edge pair can only be the identity class
            return True
        if not ok(i0): continue
        def dfs(t):
            global ngeo
            if t==4:
                ngeo+=1; tuples[tuple(lab[i] for i in order)].add(str(pr)); return
            i=order[t]
            # candidates: labels adjacent to some already-labelled class
            cand=None
            for x,y,q in cons:
                if y==i and x in lab: s=N.get((lab[x],q),set())
                elif x==i and y in lab: s=N.get((lab[y],q),set())
                else: continue
                cand=set(s) if cand is None else cand&s
            if cand is None: cand=set(classes)
            for c in sorted(cand):
                lab[i]=c
                if ok(i): dfs(t+1)
                del lab[i]
        dfs(1)
print('labelled geometries',ngeo,'distinct label tuples',len(tuples))
cnt=collections.Counter(sum(1 for c in t if len(c)==2) for t in tuples)
print('tuples by number of three-term classes:',dict(cnt))
json.dump([dict(cls=[list(c) for c in t],geo=sorted(g)) for t,g in sorted(tuples.items())],open('glue_k4_tuples.json','w'))
