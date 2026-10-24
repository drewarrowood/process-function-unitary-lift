"""Sanity check for shgrp_dfs.compat: every admissible random struct3 cube must be accepted by compat on all 28 pairs."""
import numpy as np, random, json
src=open('shgrp_dfs.py').read().split('\nS=json.load')[0]; exec(src)
import struct3
random.seed(5); ok=0; bad=0
nk=[]
for t in range(300):
    r=struct3.random_structure(pnew=0.9)
    if r is None: continue
    A,C=r; P0=A[0][0]
    st={o:np.array([A[o][0]^P0, IDX[tuple(x for x in C[A[o][1]] if x is not None)], A[o][2]]) for o in range(8)}
    # same class index in struct3 <-> same k here only if identical generators; compat allows both readings
    good=all(compat(st[o][None],st[q][None],o^q)[0] for o in range(8) for q in range(o+1,8))
    ok+=good; bad+=not good; nk.append(len(set(A[o][1] for o in range(8))))
from collections import Counter
print('accepted',ok,'rejected',bad,'classes per cube',sorted(Counter(nk).items()))
