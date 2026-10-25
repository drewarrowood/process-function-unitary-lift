"""Round 19 (H.26.2): Lasserre (moment-SOS) level-2 relaxation of the H.12 objective on the family of H.25.2
(deterministic outputs o_{k,x}, projective a-measurements along unit Bloch vectors n_{k,x}), for every one of the 64 output
patterns O.  f_O(n) = sum_x sum_mu W^O_x[mu] prod_k v_{k,x_k}[mu_k] is a cubic in 18 variables on (S^2)^6; level 2 uses the
190x190 moment matrix (monomials of degree <= 2) with the sphere equalities localised up to degree 4.
Each relaxation value is a lower bound on min f_O; if min_O of the bounds equals -0.70580 the family optimum is global.
Usage: h19_h12_lasserre.py [patterns: all | comma list of 0..63]"""
import sys, itertools as it, numpy as np, cvxpy as cp
src=open('h18_h12_local.py').read(); src=src[:src.index("E=np.load")]
exec(src)          # defines y, t[o,mu] (mp), B3, MU, d via below
import mpmath as mp
dd={}
for xi,x in enumerate(B3):
    for Ssub in it.product((0,1),repeat=3):
        dd[x,Ssub]=sum(int(y[xi,ai])*(-1)**sum(a[k] for k in range(3) if Ssub[k]) for ai,a in enumerate(B3))/8
tf={key:float(v) for key,v in t.items()}
VAR=[(k,x,c) for k in range(3) for x in range(2) for c in range(3)]; vi={v:i for i,v in enumerate(VAR)}; nv=18
def poly(O):     # dict: sorted tuple of variable indices -> coeff
    P={}
    for x in B3:
        ox=B3.index(tuple(int(O[k][x[k]]) for k in range(3)))
        for mu in MU:
            c=tf[ox,mu]*dd[x,tuple(int(m>0) for m in mu)]
            if c==0: continue
            key=tuple(sorted(vi[(k,x[k],mu[k]-1)] for k in range(3) if mu[k])); P[key]=P.get(key,0)+c
    return P
mons2=[()]+[(i,) for i in range(nv)]+[(i,j) for i in range(nv) for j in range(i,nv)]
allm={}
def mid(m):
    m=tuple(sorted(m))
    if m not in allm: allm[m]=len(allm)
    return allm[m]
for a in mons2:
    for b in mons2: mid(a+b)
nm=len(allm); print('moment variables',nm,flush=True)
def relax(O):
    P=poly(O); yv=cp.Variable(nm)
    import scipy.sparse as sp
    Mi=np.array([[allm[tuple(sorted(a+b))] for b in mons2] for a in mons2]).ravel(); L=len(mons2)
    A=sp.csr_matrix((np.ones(L*L),(np.arange(L*L),Mi)),shape=(L*L,nm))
    M=cp.reshape(A@yv,(L,L),order='C')
    cons=[yv[allm[()]]==1, M>>0]; rows=[]
    for k in range(3):
        for x in range(2):
            q=[vi[(k,x,c)] for c in range(3)]
            for m in mons2:
                rows.append({allm[tuple(sorted(m+(i,i)))]:1.0 for i in q}); rows[-1][allm[tuple(sorted(m))]]=rows[-1].get(allm[tuple(sorted(m))],0)-1.0
    r,c_,v_=zip(*[(ri,j,val) for ri,dct in enumerate(rows) for j,val in dct.items()])
    cons.append(sp.csr_matrix((v_,(r,c_)),shape=(len(rows),nm))@yv==0)
    cv=np.zeros(nm)
    for k,c in P.items(): cv[allm[k]]+=c
    obj=cv@yv
    pr=cp.Problem(cp.Minimize(obj),cons); pr.solve(solver='SCS',eps=1e-8,max_iters=50000)
    return pr.value, pr.status
pats=list(it.product((0,1),repeat=6))
sel=range(64) if len(sys.argv)<2 or sys.argv[1]=='all' else [int(s) for s in sys.argv[1].split(',')]
res=[]
for pi in sel:
    O=[[pats[pi][2*k],pats[pi][2*k+1]] for k in range(3)]
    v,st=relax(O); res.append((v,pi)); print(f'pattern {pi} O={O}: level-2 bound {v:.9f} ({st})',flush=True)
res.sort(); print('smallest bounds:',[(round(v,7),p) for v,p in res[:6]])
