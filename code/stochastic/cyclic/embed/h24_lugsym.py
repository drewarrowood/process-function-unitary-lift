"""Round 24 (H.31.1): the 16 Lugano-type cases reduce to one.
(a) Input-bit flips z -> z xor m (absorbed into the frames, X_k e_k is again a frame, and into the source) map PF phase boards on a
    Lugano-type rule w' to PF phase boards on the rule with blocks x_k(z xor m): the statistic sets are identical (no relabelling of i or o).
    We check that the 8 flips of rule 4 give exactly the 8 Lugano-type rules.
(b) Each Lugano-type phase component (H.29.3) lies inside the PF phase boards of one Lugano-type rule: every kernel vector's phase
    function phi(o,z) = x.m(o,z) lies in span{o_k x_k(z)} + span{functions of z} + span{functions of o}  (exact rank, sympy).
(c) Every PF phase board on a Lugano-type rule lies in a Lugano component (converse), checked the same way.
So all 16 Lugano-type cases have the same statistic set as PF phase boards on rule 4 (exact)."""
import json, itertools as it, numpy as np, sympy as sp
from h23_span import MAXI, mono
from h20_common import B3, others
LUG=[4,5,6,7,10,11,14,15]; LC=[7,8,9,10,22,23,24,25]
C=json.load(open('h22_pp_components.json'))
def canonparts(p): 
    m={}; return tuple(m.setdefault(b,len(m)) for b in p)
def flip(parts,mask):
    out=[]
    for k in range(3):
        newp=[]
        for j in range(4):
            # j = index of z_{-k}; find z with others(k,z)==j, flip, read block
            z=next(z for z in range(8) if others(k,z)==j and B3[z][k]==0); zf=z^mask
            newp.append(parts[k][others(k,zf)])
        out.append(canonparts(newp))
    return tuple(out)
rules={tuple(canonparts(p) for p in MAXI[w]):w for w in LUG}
imgs=[rules.get(flip(MAXI[4],m)) for m in range(8)]
print('(a) z-flip images of rule 4 ->',imgs,'all 8 Lugano rules:',sorted(imgs)==LUG)
def board_space(w):
    cols=[]
    for k in range(3):
        cols.append([B3[o][k]*MAXI[w][k][others(k,z)] for o in range(8) for z in range(8)])
    for z0 in range(8): cols.append([int(z==z0) for o in range(8) for z in range(8)])
    for o0 in range(8): cols.append([int(o==o0) for o in range(8) for z in range(8)])
    return sp.Matrix(cols).T
def kerQ(M): return sp.Matrix(M).nullspace()
res={}
for ci in LC:
    K=kerQ(C[ci]['rows']); found=[]
    for w in LUG:
        B=board_space(w); r=B.rank(); ok=True
        for v in K:
            phi=sp.Matrix([sum(v[m]*int(mono[o,z,m]) for m in range(12)) for o in range(8) for z in range(8)])
            if B.row_join(phi).rank()!=r: ok=False; break
        if ok:
            # converse: each o_k x_k(z) column lies in span(comp functions) + z-only + o-only
            Fc=[sp.Matrix([sum(v[m]*int(mono[o,z,m]) for m in range(12)) for o in range(8) for z in range(8)]) for v in K]
            base=sp.Matrix.hstack(*Fc,*[B.col(3+t) for t in range(16)]); rb=base.rank()
            conv=all(base.row_join(B.col(k)).rank()==rb for k in range(3))
            found.append((w,conv))
    res[ci]=found; print('(b,c) component',ci,'dim',len(K),'-> rules (w, converse):',found,flush=True)
