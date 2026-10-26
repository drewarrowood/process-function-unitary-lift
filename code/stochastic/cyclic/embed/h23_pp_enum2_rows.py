"""the 1219 branch lattices of H.29.3 (same construction as h22_pp_components.py)"""
import itertools as it, numpy as np, sympy
def branches():
    def a(k,j): return [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)].index((k,j))
    rows_all={}
    for (j,k) in [(0,1),(0,2),(1,2)]:
        for zl,ol in it.product((0,1),repeat=2):
            Rj=np.zeros(12,int); Rj[a(j,k)]=1; Rj[6+j]+=zl; Rj[9+k]+=ol
            Rk=np.zeros(12,int); Rk[a(k,j)]=1; Rk[6+k]+=zl; Rk[9+j]+=ol
            rows_all[(j,k,zl,ol)]=(Rj,Rk)
    keys=list(rows_all); br={}
    for choice in it.product((0,1),repeat=12):
        M=np.unique(np.array([rows_all[kk][c] for kk,c in zip(keys,choice)]),axis=0)
        R=sympy.Matrix(M).rref()[0]; key=tuple(tuple(R.row(i)) for i in range(R.rows) if any(R.row(i))); br.setdefault(key,M)
    return list(br.values())
