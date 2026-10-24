"""H.17.8(c) quick sample [numerical, generic-support model]: does SH_grp (shadows closed to groups <x_A,x_B>) hold on random
admissible hard <=3-term structures from struct3?  Time-boxed sample, not exhaustive."""
import sys, time, json, random
import numpy as np
from struct3 import *
seed=int(sys.argv[1]); T=float(sys.argv[2]); random.seed(seed); np.random.seed(seed)
def grp(sh):
    G={0}
    for t in sh: G|={g^t for g in G}
    return sorted(G)
def SHgrp(assign,classes):
    tc={o:tclass(assign,classes,o) for o in range(8)}; bad=0; gapcls=0
    for o in range(8):
        for q in range(o+1,8):
            if tc[o]==tc[q]: continue
            D=o^q; a=px(assign[o][0])^px(assign[q][0])
            if any(not allowedX(a^t^t2,D) for t in grp(shadow(classes,tc[o])) for t2 in grp(shadow(classes,tc[q]))): bad+=1
    return bad
res=dict(structs=0,hard=0,hard_with_gap_class=0,sh_fail=0,shgrp_fail=0); t0=time.time()
while time.time()-t0<T:
    r=random_structure()
    if r is None: continue
    A,C=r; res['structs']+=1
    if not any(c[0]==3 for c in C) or any(first_last(A,C)): continue
    res['hard']+=1
    res['hard_with_gap_class']+=any(c[0]==3 and len({0,*(px(g) for g in gens(c))})==3 and (px(gens(c)[0])^px(gens(c)[1])) not in (0,) and len(grp([px(g) for g in gens(c)]))==4 for c in C)
    res['sh_fail']+=bool(SH(A,C)); res['shgrp_fail']+=SHgrp(A,C)>0
print(json.dumps(res))
