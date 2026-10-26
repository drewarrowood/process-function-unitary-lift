"""Round 23 (H.30.2): complete the enumeration of valid three-qubit phase processes (H.29.3).
(a) Torsion: for every one of the 1219 branch lattices, Smith normal form; for branches with an invariant d > 1 the solution set
    {x : M x in 2 pi Z^r} has extra cosets x0 + ker M; each coset is tested for validity (pen at random points) and, if valid,
    for containment in one of the 34 components.
(b) The 2 branches that fail the three-party condition at random points: minimise pen over the branch (ker M plus cosets) from
    many random starts; every valid point found is tested for membership in the 34 components (distance of M_c x to 2 pi Z).
usage: NSTART seed"""
import sys, itertools as it, numpy as np, torch, sympy, json
from sympy.matrices.normalforms import smith_normal_form
from h22_copp import pen
from h22_phaseproc import U_of
torch.set_default_dtype(torch.float64)
NS=int(sys.argv[1]); rng=np.random.default_rng(int(sys.argv[2]))
def a(k,j): return [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)].index((k,j))
rows_all={}
for (j,k) in [(0,1),(0,2),(1,2)]:
    l=3-j-k
    for zl,ol in it.product((0,1),repeat=2):
        Rj=np.zeros(12,int); Rj[a(j,k)]=1; Rj[6+j]+=zl; Rj[9+k]+=ol
        Rk=np.zeros(12,int); Rk[a(k,j)]=1; Rk[6+k]+=zl; Rk[9+j]+=ol
        rows_all[(j,k,zl,ol)]=(Rj,Rk)
keys=list(rows_all)
def rkey(M):
    R=sympy.Matrix(M).rref()[0]; return tuple(tuple(R.row(i)) for i in range(R.rows) if any(R.row(i)))
br={}
for choice in it.product((0,1),repeat=12):
    M=np.unique(np.array([rows_all[kk][c] for kk,c in zip(keys,choice)]),axis=0); br.setdefault(rkey(M),M)
print(len(br),'branch lattices',flush=True)
C=json.load(open('h22_pp_components.json')); CM=[np.array(c['rows']) for c in C]
def in_comp(x,tol=1e-7):
    out=[]
    for ci,M in enumerate(CM):
        r=M@x/(2*np.pi); 
        if np.abs(r-np.round(r)).max()<tol: out.append(ci)
    return out
def kerN(M):
    r=np.linalg.matrix_rank(M.astype(float)); _,_,Vt=np.linalg.svd(M.astype(float)); return Vt[r:].T
def cosets(M):
    """coset representatives x0 of {x: M x in 2 pi Z^r} modulo ker M + 2 pi Z^12 (from the Smith form U M V = D)"""
    Ms=sympy.Matrix(M); D,U,V=None,None,None
    from sympy.matrices.normalforms import smith_normal_decomp
    D,U,V=smith_normal_decomp(Ms,domain=sympy.ZZ)
    inv=[int(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0]
    reps=[]
    for t in it.product(*[range(abs(d)) for d in inv]):
        w=np.zeros(Ms.cols); 
        for i,(ti,d) in enumerate(zip(t,inv)): w[i]=2*np.pi*ti/abs(d)
        reps.append(np.array(V,dtype=float)@w)
    return inv,reps
def rand_pen(x0,N,n=4):
    ps=[]
    for _ in range(n):
        x=x0+N@rng.uniform(-np.pi,np.pi,N.shape[1])*3; ps.append(float(pen(U_of(torch.tensor(np.r_[x,rng.uniform(-np.pi,np.pi,9)])))))
    return max(ps)
tors=0; newcos=[]; failing=[]
for k,M in br.items():
    N=kerN(M); inv,reps=cosets(M)
    if rand_pen(np.zeros(12),N)>1e-18: failing.append(M)
    if any(abs(d)>1 for d in inv):
        tors+=1
        for x0 in reps[1:]:
            if rand_pen(x0,N)<1e-18:
                x=x0+N@rng.uniform(-np.pi,np.pi,N.shape[1]); ic=in_comp(x)
                if not ic: newcos.append((M.tolist(),x0.tolist()))
print('branches with torsion:',tors,'; valid torsion cosets not inside the 34 components:',len(newcos),flush=True)
print('failing branches:',len(failing),flush=True)
res=[]
for bi,M in enumerate(failing):
    N=kerN(M); inv,reps=cosets(M); found=[]; nval=0
    print('failing branch',bi,'rows',M.tolist(),'Smith invariants',inv,'ker dim',N.shape[1],flush=True)
    for s in range(NS):
        x0=reps[rng.integers(len(reps))]; y=torch.tensor(rng.uniform(-np.pi,np.pi,N.shape[1])*3,requires_grad=True); fr=torch.tensor(rng.uniform(-np.pi,np.pi,9))
        Nt=torch.tensor(N); x0t=torch.tensor(x0)
        opt=torch.optim.LBFGS([y],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
        def clo():
            opt.zero_grad(); v=pen(U_of(torch.cat([x0t+Nt@y,fr]))); v.backward(); return v
        opt.step(clo); x=(x0t+Nt@y).detach().numpy(); pv=float(pen(U_of(torch.cat([torch.tensor(x),fr]))))
        if pv<1e-20:
            nval+=1; ic=in_comp(x,1e-6)
            if not ic: found.append(x.tolist())
    print(f'  {NS} starts: {nval} reach pen<1e-20; valid points outside the 34 components: {len(found)}',flush=True)
    res.append(dict(rows=M.tolist(),inv=inv,nvalid=nval,outside=found[:20]))
json.dump(dict(torsion_branches=tors,new_cosets=newcos,failing=res),open('h23_pp_enum2.json','w'))
