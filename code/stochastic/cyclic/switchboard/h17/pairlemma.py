"""H.17.2 [exhaustive, exact]: pairwise check.  For every anticommuting Hermitian pair (A,B), every sign change ds in {1,2,3},
every pair of left Paulis (P,P') (wlog P=0 by translation: only R = P xor P' matters) and every output difference D != 0:
if the generic support R + S(ds) avoids all forbidden strings (Pauli rule for the pair), do the X-shadows
x_R + t + t' (t,t' in {0,x_A,x_B}) avoid the forbidden X-strings (x & D == D)?"""
from struct3 import *
fails=[];cnt=0
for a,b in ANTI:
    c=(3,a,b)
    for ds in (1,2,3):
        S=S_same(c,ds)
        for R in range(64):
            for D in range(1,8):
                if any(FORB[D][R^s] for s in S): continue
                cnt+=1
                sh={0,px(a),px(b)}
                if any((px(R)^t^u)&D==D for t in sh for u in sh): fails.append((a,b,ds,R,D))
print('admissible (pair,ds,R,D) cases:',cnt,' SH failures:',len(fails))
import collections
print(collections.Counter((f[2],f[4]) for f in fails).most_common(10))
print(fails[:10])
