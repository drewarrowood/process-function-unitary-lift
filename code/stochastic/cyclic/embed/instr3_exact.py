"""H.15.7e(B): exact certificate that 'nice' (cube-26) measurement directions already make H.12 violate a causal inequality.
Configuration found by instr3_nice.py (cube26, seed 13): agent k, setting x measures along n_{k,x} and emits a CONSTANT o_k = g:
  A: x=0 n=(1,-1,-1)/sqrt3, o=0 ; x=1 n=(0,-1,-1)/sqrt2, o=1
  B: x=0 n=(1,-1,-1)/sqrt3, o=0 ; x=1 n=(0,-1, 1)/sqrt2, o=1
  C: x=0 n=(0,0,1),         o=1 ; x=1 n=(0,0,1),          o=0
(so o = x for A, B and o = 1-x for C).  P(a|x) = <psi_o| Pi_{a|x} |psi_o>, entries in Q(i, sqrt2, sqrt3).  y is the integer
pool inequality minimising y.P; its causal bound (min over all 138,304 deterministic causal strategies) is checked in integers."""
import sys, numpy as np, itertools as it, sympy as sp, json
sys.argv=[sys.argv[0]]
import instr_search2 as S, instr_search as IS
B3=IS.B3; s2,s3=sp.sqrt(2),sp.sqrt(3)
cfg=[[((1/s3,-1/s3,-1/s3),0),((0,-1/s2,-1/s2),1)],[((1/s3,-1/s3,-1/s3),0),((0,-1/s2,1/s2),1)],[((0,0,1),1),((0,0,1),0)]]
X=sp.Matrix([[0,1],[1,0]]);Yp=sp.Matrix([[0,-sp.I],[sp.I,0]]);Z=sp.Matrix([[1,0],[0,-1]])
Pi={}
for k in range(3):
    for x in (0,1):
        n,_=cfg[k][x]; assert sp.simplify(sum(t**2 for t in n)-1)==0
        Pi[k,x,0]=(sp.eye(2)+n[0]*X+n[1]*Yp+n[2]*Z)/2; Pi[k,x,1]=sp.eye(2)-Pi[k,x,0]
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
par=lambda x:bin(x).count('1')&1
Hs=sp.Matrix(8,8,lambda a,b:(-1)**par(a&b))/sp.sqrt(8)
ph=sp.Matrix([0,0,0,1/sp.sqrt(2),(1-sp.I)/2,0,0,0])
psis=[sp.expand(Hs*sp.diag(*[sp.I**MT[o][z] for z in range(8)])*Hs*ph) for o in range(8)]
P=sp.zeros(8,8)
for xi,x in enumerate(B3):
    o=B3.index(tuple(cfg[k][x[k]][1] for k in range(3))); v=psis[o]
    for ai,a in enumerate(B3):
        M=sp.kronecker_product(Pi[0,x[0],a[0]],Pi[1,x[1],a[1]],Pi[2,x[2],a[2]])
        P[xi,ai]=sp.radsimp(sp.expand((v.H*M*v)[0]))
Pf=np.array([[complex(sp.N(P[x,a],30)) for a in range(8)] for x in range(8)]).real
m=json.load(open('../switchboard/h13/min_cex.json'))['m']; Hd=IS.Hd
U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
psiA=np.array([1,1,1,0,0,-1,0,0])/2; psiB=np.array([1,1,1,0,0,0,0,0])/np.sqrt(3); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
Yl=[]
for p in ([[abs((U13[o]@psiA)[i])**2 for i in range(8)] for o in range(8)],[[abs((U13[o]@psiB)[i])**2 for i in range(8)] for o in range(8)],[[float(B3[i]==lug(*B3[o])) for i in range(8)] for o in range(8)]):
    Yl+=S.images(S.farkas(np.array(p)))
Yl=np.unique(np.round(np.array(Yl),9),axis=0); y=Yl[np.argmin(Yl@Pf.ravel())]
yi=[int(round(t)) for t in y]; assert np.allclose(y,yi)
VA=IS.A.toarray().astype(int); print('integer inequality y (row-major x,a):',yi)
print('min over all 138,304 deterministic causal strategies (exact integers):',int((np.array(yi)@VA).min()))
print('rows sum to 1 exactly:',all(sp.simplify(sum(P[x,a] for a in range(8))-1)==0 for x in range(8)))
print('min entry (30 digits):',Pf.min())
print('distinct P entries:',sorted({str(P[x,a]) for x in range(8) for a in range(8)}))
val=sp.nsimplify(sp.radsimp(sp.expand(sum(yi[8*x+a]*P[x,a] for x in range(8) for a in range(8)))))
print('y.P exact =',val,' = ',sp.N(val,20),'; < 0:',bool(sp.N(val,50)<0))
