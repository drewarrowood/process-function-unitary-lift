"""H.17.5 [LP screen + exact certificate]: which PF-hull facet orbits remain valid on the whole valid polytope Valid?
Such a facet holds on Purif trivially (Purif <= Valid).  Valid: p(i|o)>=0, sum_i p(i|o)=1, and for every deterministic
local intervention f=(f_A,f_B,f_C), f_k:{0,1}->{0,1}, sum_i p(i|f(i)) = 1 (fixed point probability 1).
Facet functional: exact integer hyperplane from physics/facets/pf.out.gz in the 37 Z-coordinates, pulled back to p."""
import numpy as np, gzip, itertools as it, json
from fractions import Fraction as Fr
from scipy.optimize import linprog
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(int)          # [744, i, o]
Zc=np.load(F+'Z.npy').astype(int)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))])
canon=np.load('../h13/xviol.npz')['canon'].astype(int)
B3=list(it.product((0,1),repeat=3)); idx=lambda i,o: i*8+o
# equalities
Aeq=[];beq=[]
for o in range(8):
    r=np.zeros(64); r[[idx(i,o) for i in range(8)]]=1; Aeq.append(r); beq.append(1)
for f in it.product(range(4),repeat=3):            # f_k as 2-bit table: f_k(x)= (f>>x)&1
    r=np.zeros(64)
    for i in range(8):
        ib=B3[i]; ob=tuple((f[t]>>ib[t])&1 for t in range(3)); r[idx(i,B3.index(ob))]+=1
    Aeq.append(r); beq.append(1)
Aeq=np.array(Aeq); beq=np.array(beq,float)
rk=np.linalg.matrix_rank(Aeq); print('rank of validity equalities',rk,'-> affine dim',64-rk)
# linear map p -> Z (exact): solve [PF,1] M = Z in rationals via least squares then verify exactly
X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
M=np.linalg.lstsq(X.astype(float),Zc.astype(float),rcond=None)[0]
res={}
for orb in sorted(set(canon)):
    f=int(np.nonzero(canon==orb)[0][0]); h=Hm[f]
    v=Zc@h[:37]+h[37]; g=np.linalg.lstsq(X.astype(float),v.astype(float),rcond=None)[0]
    assert np.abs(X@g-v).max()<1e-9
    gv=g[:64]; g0=g[64]
    vals=PF.reshape(744,-1)@gv+g0; rng_=vals.max()
    lp=linprog(gv,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs')
    res[int(orb)]=(float((lp.fun+g0)/rng_),f)
neg=[o for o,(v,_) in res.items() if v<-1e-9]; nonneg=[o for o,(v,_) in res.items() if v>=-1e-9]
print('orbits valid on all of Valid (min >= 0):',nonneg)
NC=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81,92]
print('never-crossed orbits valid on Valid:',[o for o in NC if o in nonneg])
print('never-crossed orbits violated on Valid (min rel value):',{o:round(res[o][0],4) for o in NC if o not in nonneg})
json.dump(res,open('validlp.json','w'))
