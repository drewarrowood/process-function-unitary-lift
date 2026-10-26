"""Round 22 (H.29.3): exact classification of valid three-qubit phase processes (h22_phaseproc.py).
phi(o,z) = sum_m x_m mono_m(o,z) over the 12 mixed monomials (index: a_{k,j} = coefficient of o_k z_j (0..5), c_k = o_k z_j z_l (6..8),
g_l = o_j o_k z_l (9..11)).  For a pair {j,k} with third party l, the two-party validity condition at fixed (z_l, o_l) factorises as
   (1 - e^{i R_j})(1 - e^{i R_k}) = 0,   R_j = a_{j,k} + c_j z_l + g_k o_l,   R_k = a_{k,j} + c_k z_l + g_j o_l,
so each of the 12 (pair, z_l, o_l) conditions says R_j = 0 or R_k = 0 (mod 2 pi): one-way influence, as for process functions.
A choice of one alternative per condition (4096 branches) is a system of integer linear congruences.  We compute its solution set
(Smith normal form: torsion-free branches are subtori x = N y), keep the maximal distinct ones, and test the three-party condition
(and the full criterion pen) at random points of each.  Output: list of maximal valid components with dimension."""
import itertools as it, numpy as np, torch, sympy, json, sys
from sympy.matrices.normalforms import smith_normal_form
from h22_copp import pen
from h22_phaseproc import U_of
def a(k,j): return [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)].index((k,j))
rows_all={}
for (j,k) in [(0,1),(0,2),(1,2)]:
    l=3-j-k
    for zl,ol in it.product((0,1),repeat=2):
        Rj=np.zeros(12,int); Rj[a(j,k)]=1; Rj[6+j]+=zl; Rj[9+k]+=ol
        Rk=np.zeros(12,int); Rk[a(k,j)]=1; Rk[6+k]+=zl; Rk[9+j]+=ol
        rows_all[(j,k,zl,ol)]=(Rj,Rk)
keys=list(rows_all)
def rspace_key(M):
    if len(M)==0: return ()
    R=sympy.Matrix(M).rref()[0]; R=[tuple(R.row(i)) for i in range(R.rows) if any(R.row(i))]; return tuple(R)
comps={}
for choice in it.product((0,1),repeat=12):
    M=np.array([rows_all[kk][c] for kk,c in zip(keys,choice)])
    M=np.unique(M,axis=0); comps.setdefault(rspace_key(M),M)
print(len(comps),'distinct branch row spaces',flush=True)
rng=np.random.default_rng(0)
def rank(M): return np.linalg.matrix_rank(np.array(M,float)) if len(M) else 0
def test(M):
    r=rank(M); _,_,Vt=np.linalg.svd(np.array(M,float)); N=Vt[r:].T; pens=[]
    for t in range(4):
        xx=torch.tensor(np.r_[N@rng.uniform(-np.pi,np.pi,N.shape[1])*3,rng.uniform(-np.pi,np.pi,9)]); pens.append(float(pen(U_of(xx))))
    return r,max(pens)
items=[]; nfail=0
for k,M in comps.items():
    r,p=test(M)
    if p<1e-18: items.append((k,M,r))
    else: nfail+=1
print(len(items),'branches valid at all test points (three-party condition automatic);',nfail,'fail the three-party condition somewhere',flush=True)
maxi=[]
for k,M,r in items:
    if not any(r2<r and rank(np.vstack([M,M2]))==r for k2,M2,r2 in items): maxi.append((k,M,r))
print(len(maxi),'maximal valid components (by real row space)',flush=True)
out=[]
for k,M,r in maxi:
    D=smith_normal_form(sympy.Matrix(M),domain=sympy.ZZ); inv=[int(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0]
    used=sorted({int(j) for j in np.nonzero(np.array(M).sum(0))[0]})
    _,_,Vt=np.linalg.svd(np.array(M,float)); N=Vt[r:].T
    free=[j for j in range(12) if np.abs(N[j]).max()>1e-9]
    out.append(dict(rows=np.array(M).astype(int).tolist(),dim=int(12-r),inv=inv,free=free))
    print(f'dim {12-r}, invariants all 1: {all(abs(d)==1 for d in inv)}, nonzero coordinates {free}',flush=True)
json.dump(out,open('h22_pp_components.json','w'))
