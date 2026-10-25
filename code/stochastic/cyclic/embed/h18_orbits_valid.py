"""Round 18 (H.25.4): the 10 never-crossed orbits are not implied by validity alone.
For one representative facet of each open orbit (orbits are Purif-symmetric, H.23.1a), minimise the (relative) facet functional
over Valid, the Baumeler-Wolf polytope of valid classical processes p(i|o): p >= 0, sum_i p(i|o) = 1 and, for each of the 64
deterministic local interventions f, sum_i p(i | f(i)) = 1 (classical logical consistency).  The minimiser is then rounded to a
rational point and checked EXACTLY: it is a valid classical process (all constraints in Fractions) with negative facet value.
Valid processes are realised by diagonal (hence valid, generally mixed) process matrices, so no argument that uses only
validity of the process matrix (SDP relaxations without a purity/rank condition) can prove these facets on Purif.  [PROVED]"""
import itertools as it, numpy as np, gzip
from fractions import Fraction as Fr
from scipy.optimize import linprog
F='../../physics/facets/'
B3=list(it.product((0,1),repeat=3))
PF=np.load('../pfs744.npy').astype(int); Zc=np.load(F+'Z.npy').astype(float)
print('PF array shape',PF.shape,' row sums over axis 1:',set(PF.sum(1).ravel().tolist()),' axis 2:',set(PF.sum(2).ravel().tolist()))
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
canon=np.load('../switchboard/h13/xviol.npz')['canon'].astype(int)
OPEN=[26,28,30,31,54,57,66,69,75,81]
Zi=np.load(F+'Z.npy').astype(np.int64); Hi=Hm.astype(np.int64); valsI=Zi@Hi[:,:37].T+Hi[:,37]   # exact integer facet values on the 744 PFs
assert (valsI>=0).all()
# equality constraints of Valid on p[i,o] (vector index 8*i+o)
Aeq=[];beq=[]
for o in range(8):
    r=np.zeros(64); r[[8*i+o for i in range(8)]]=1; Aeq.append(r); beq.append(1)
funcs=list(it.product(range(4),repeat=3))   # f_k: I_k -> O_k, 4 maps per party (bit -> bit)
fmap=lambda m,b:[0,1,b,1-b][m]
for fm in funcs:
    r=np.zeros(64)
    for i in range(8):
        ib=B3[i]; ob=tuple(fmap(fm[k],ib[k]) for k in range(3)); r[8*i+B3.index(ob)]+=1
    Aeq.append(r); beq.append(1)
Aeq=np.array(Aeq); beq=np.array(beq)
assert np.allclose(Aeq@PF.reshape(744,64).T,1)
# 38 affinely independent PFs for exact affine coordinates
def exact_affine_basis():
    M=np.c_[PF.reshape(744,64),np.ones(744)]; idx=[]; cur=np.zeros((0,65))
    for n in range(744):
        if np.linalg.matrix_rank(np.r_[cur,M[n:n+1]])>len(idx): idx.append(n); cur=np.r_[cur,M[n:n+1]]
        if len(idx)==38: break
    return idx
BI=exact_affine_basis(); print('affine basis of PFs:',len(BI))
def solve_exact(Mrows,rhs):   # least squares exact: solve normal equations in Fractions (system consistent)
    A_=[[Fr(int(x)) for x in row] for row in Mrows]; b_=[Fr(x) for x in rhs]; m=len(A_); n=len(A_[0])
    N=[[sum(A_[r][i]*A_[r][j] for r in range(m)) for j in range(n)] for i in range(n)]; c=[sum(A_[r][i]*b_[r] for r in range(m)) for i in range(n)]
    for col in range(n):
        piv=next(r for r in range(col,n) if N[r][col]!=0); N[col],N[piv]=N[piv],N[col]; c[col],c[piv]=c[piv],c[col]
        for r in range(n):
            if r!=col and N[r][col]!=0:
                f=N[r][col]/N[col][col]; N[r]=[a-f*b for a,b in zip(N[r],N[col])]; c[r]-=f*c[col]
    return [c[i]/N[i][i] for i in range(n)]
Mb=np.c_[PF[BI].reshape(38,64),np.ones(38)].T   # 65 x 38
for orb in OPEN:
    fidx=int(np.where(canon==orb)[0][0])
    res=linprog(Tn[fidx,:64],A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs')
    p=res.x; D=840
    # round to a rational valid point: round, then verify exactly; if rounding breaks validity, use the LP vertex's support
    pq=[Fr(int(round(x*D)),D) for x in p]
    okv=all(x>=0 for x in pq) and all(sum(Fr(int(Aeq[r,j]))*pq[j] for j in range(64))==1 for r in range(len(Aeq)))
    if not okv:
        # exact vertex: solve the active equality system on the support in Fractions
        sup=[j for j in range(64) if p[j]>1e-9]
        sol=solve_exact(Aeq[:,sup],beq); pq=[Fr(0)]*64
        for j,v in zip(sup,sol): pq[j]=v
        okv=all(x>=0 for x in pq) and all(sum(Fr(int(Aeq[r,j]))*pq[j] for j in range(64))==1 for r in range(len(Aeq)))
    lam=solve_exact(Mb,[*pq,Fr(1)])
    chk=all(sum(lam[n]*int(Mb[r,n]) for n in range(38))==([*pq,Fr(1)][r]) for r in range(65))
    val=sum(lam[n]*int(valsI[BI[n],fidx]) for n in range(38)); rel=val/int(valsI[:,fidx].max())
    print(f'orbit {orb}: representative facet {fidx}; LP min over Valid (relative) {res.fun+Tn[fidx,64]:.6f}; exact rational valid point: {okv}, affine coords exact: {chk}, exact relative facet value {rel} = {float(rel):.6f}',flush=True)
