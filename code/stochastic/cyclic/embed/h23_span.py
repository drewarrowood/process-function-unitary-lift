"""Round 23 (H.30.1): the linear span S that contains all statistics of a family, from the expansion
   p(i|o) = sum_{z,z'} conj(psi_z) psi_z' * chi_{zz'}(o) * prod_k conj(e_k[i_k,z_k]) e_k[i_k,z'_k].
Frame factor (any SU(2) frame e_k): as a function of i_k it lies in span{1,(-1)^i} if z_k = z'_k and in span{(-1)^i} if z_k != z'_k
(columns of a unitary are orthogonal).  o-factor chi:
 - phase-process component (rows M, integer, torsion-free): chi = exp(i <x, m(o,z') - m(o,z)>) with x in ker M (mod 2 pi);
   as x varies it lies in the span of the indicators of the classes  o ~ o'  <=>  [m(o,z')-m(o,z)] - [m(o',z')-m(o',z)] in rowspace(M).
 - time-reversed PF lift on refined PF w' (H.27.2 / Lemma H.29.2a): chi = prod_k K_k(o_k)[x_k(z), x_k(z')]; the factor for party k is
   1 if x_k(z) = x_k(z') and an arbitrary function of o_k otherwise.
So every statistic lies in S = span of (o-pattern) (x) (i-pattern) over pairs (z,z').  Exact (integer generators, sympy ranks).
This module builds S; run as a script it compares S with sampled statistics and computes float LP minima over Valid ∩ S."""
import sys, json, itertools as it, numpy as np, sympy as sp
from h20_common import B3, others
C=json.load(open('h22_pp_components.json'))
E=json.load(open('h20_fwd_enum.json')); MAXI=[tuple(map(tuple,p)) for p in E['maximal']]
from h22_phaseproc import MONO
mono=np.array([[[int(all(B3[o][a] for a in m[0]) and all(B3[z][b] for b in m[1])) for m in MONO] for z in range(8)] for o in range(8)])  # [o,z,12]
def ipat(z,zp):
    """generators (length-8 integer vectors over i) for the frame factor"""
    facs=[[(1,1),(1,-1)] if B3[z][k]==B3[zp][k] else [(1,-1)] for k in range(3)]
    return [np.array([f0[B3[i][0]]*f1[B3[i][1]]*f2[B3[i][2]] for i in range(8)]) for f0,f1,f2 in it.product(*facs)]
def opat_comp(ci,z,zp):
    M=sp.Matrix(C[ci]['rows']); r=M.rank(); v=[mono[o,zp]-mono[o,z] for o in range(8)]; cls=[]
    for o in range(8):
        for c in cls:
            if sp.Matrix.vstack(M,sp.Matrix([list(v[o]-v[c[0]])])).rank()==r: c.append(o); break
        else: cls.append([o])
    return [np.array([int(o in c) for o in range(8)]) for c in cls]
def opat_rule(wi,z,zp):
    parts=MAXI[wi]; facs=[]
    for k in range(3):
        same=parts[k][others(k,z)]==parts[k][others(k,zp)]
        facs.append([(1,1)] if same else [(1,1),(1,-1)])
    return [np.array([f0[B3[o][0]]*f1[B3[o][1]]*f2[B3[o][2]] for o in range(8)]) for f0,f1,f2 in it.product(*facs)]
def span_gens(opat):
    G=[]
    for z in range(8):
        for zp in range(8):
            for po in opat(z,zp):
                for pi in ipat(z,zp): G.append(np.outer(pi,po).ravel())   # index 8*i+o, matches Tn[f,:64].reshape(8,8)[i,o]
    G=np.unique(np.array(G),axis=0); return G
def basis(G):
    """integer basis (subset of generators) of span(G), exact"""
    Mx=sp.Matrix(G.T.tolist()); _,piv=Mx.rref(); return G[list(piv)]
