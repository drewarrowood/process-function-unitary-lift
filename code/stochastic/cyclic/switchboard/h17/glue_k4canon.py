"""H.17.17: keep one labelled geometry per orbit under cube translations x G48 (qubit permutations acting on strings and
cube directions together, and S-conjugations), both PROVED symmetries (H.17.15(d)).  Writes glue_k4_canon.json."""
import json, ast
from t3sym import G, cls_act, pbits
from glue_k4 import items
def key(lab):   # lab[v] = (label, cid)
    best=None
    for g in G:
        pi,m=g
        for t in range(8):
            new={}
            for v in range(8):
                L,c=lab[v]; w=pbits(v,pi)^t
                new[w]=(cls_act(g,L) if L else (),c)
            ren={}; tup=[]
            for w in range(8):
                L,c=new[w]; ren.setdefault(c,len(ren)); tup.append((L,ren[c]))
            tup=tuple(tup)
            if best is None or tup<best: best=tup
    return best
seen={}; 
for gi,L,cid in items():
    k=key({v:(L[cid[v]],cid[v]) for v in range(8)}); seen.setdefault(k,gi)
print('geometries',gi+1,'distinct up to translations x G48',len(seen))
json.dump(sorted(seen.values()),open('glue_k4_canon.json','w'))
