"""EXACT verification (rational arithmetic in Q(zeta_8), zeta^4 = -1) of the X-type switchboard counterexample.
Board: U_o = Hd diag(i^{k_o(z)/2}) Hd with k from cex_phases.json (multiples of pi/4, all even => 4th roots of 1).
Source phi = (|3> + zeta^7 |4>)/sqrt2.  Checks: (1) U_o unitary; (2) Pauli rule H.8.1 for all o != o' (=> pure,
with and without ancillas, by H.8.1-H.8.2); (3) p(i|o)=|<i|U_o phi>|^2 is real, a valid classical process (all 64
deterministic interventions sum to 1); (4) an integer inequality g.p + g0 >= 0, valid on all 744 PFs (checked exactly),
is violated by p (sign of a + b sqrt2 decided exactly).  Uses no floating point."""
import json, itertools as it
from fractions import Fraction as Fr
class Q8:
    __slots__=('c',)
    def __init__(s,c): s.c=tuple(Fr(x) for x in c)
    def __add__(s,o): return Q8([a+b for a,b in zip(s.c,o.c)])
    def __sub__(s,o): return Q8([a-b for a,b in zip(s.c,o.c)])
    def __mul__(s,o):
        r=[Fr(0)]*8
        for i,a in enumerate(s.c):
            if a:
                for j,b in enumerate(o.c):
                    if b: r[i+j]+=a*b
        return Q8([r[0]-r[4],r[1]-r[5],r[2]-r[6],r[3]-r[7]])
    def conj(s):  # zeta -> zeta^7 = -zeta^3, zeta^2 -> -zeta^2, zeta^3 -> -zeta
        a,b,c,d=s.c; return Q8([a,-d,-c,-b])
    def iszero(s): return all(x==0 for x in s.c)
    def __eq__(s,o): return (s-o).iszero()
def z(k): k%=8; v=[0]*4; v[k%4]=1 if k<4 else -1; return Q8(v)
ZERO=Q8([0]*4); ONE=z(0); SQ2=Q8([0,1,0,-1]); HALF=Q8([Fr(1,2),0,0,0])
B3=list(it.product((0,1),repeat=3))
k=json.load(open('cex_phases.json'))
inv8=SQ2*Q8([Fr(1,4),0,0,0])                  # 1/sqrt8 = sqrt2/4
H=[[inv8*(ONE if sum(a*b for a,b in zip(B3[x],B3[y]))%2==0 else Q8([-1,0,0,0])) for y in range(8)] for x in range(8)]
def mm(A,B): return [[sum((A[i][l]*B[l][j] for l in range(8)),ZERO) for j in range(8)] for i in range(8)]
def dag(A): return [[A[j][i].conj() for j in range(8)] for i in range(8)]
U=[mm(mm(H,[[z(k[o][x]) if x==y else ZERO for y in range(8)] for x in range(8)]),H) for o in range(8)]
I8=[[ONE if i==j else ZERO for j in range(8)] for i in range(8)]
assert all(mm(U[o],dag(U[o]))==I8 for o in range(8)); print('(1) all U_o unitary: exact')
def pauli(a,b):  # matrix of X^a Z^b (entries 0, +-1)
    M=[[ZERO]*8 for _ in range(8)]
    for e in range(8):
        eb=B3[e]; sgn=(-1)**sum(bb*x for bb,x in zip(b,eb)); r=B3.index(tuple(x^y for x,y in zip(eb,a)))
        M[r][e]=Q8([sgn,0,0,0])
    return M
P={(a,b):pauli(a,b) for a in B3 for b in B3}
bad=0; nchk=0
for o in range(8):
    for q in range(8):
        if o==q: continue
        Kq=mm(U[o],dag(U[q])); Dl=[t for t in range(3) if B3[o][t]!=B3[q][t]]
        for (a,b),S in P.items():
            if all(a[t] or b[t] for t in Dl):
                tr=sum((S[j][i].conj()*Kq[j][i] for i in range(8) for j in range(8)),ZERO); nchk+=1
                if not tr.iszero(): bad+=1
print('(2) forbidden Pauli coefficients checked',nchk,'nonzero',bad); assert bad==0
phi=[ZERO]*8; phi[3]=SQ2*HALF; phi[4]=z(7)*SQ2*HALF
p=[[None]*8 for _ in range(8)]
for o in range(8):
    for i in range(8):
        amp=sum((U[o][i][s]*phi[s] for s in range(8)),ZERO); v=amp*amp.conj()
        assert v.c[2]==0 and v.c[1]==-v.c[3]       # real: a + b*sqrt2 with sqrt2 = zeta - zeta^3
        p[i][o]=(v.c[0],v.c[1])                     # value = a + b sqrt2
print('(3a) p is real, entries in Q(sqrt2)')
def add(x,y): return (x[0]+y[0],x[1]+y[1])
for o in range(8): assert sum(p[i][o][0] for i in range(8))==1 and sum(p[i][o][1] for i in range(8))==0
def sgn(x):  # sign of a + b sqrt2
    a,b=x
    if a>=0 and b>=0: return (a>0 or b>0)*1
    if a<=0 and b<=0: return -1*((a<0) or (b<0))
    s=1 if a>0 else -1; return s if a*a>2*b*b else (-s if a*a<2*b*b else 0)
assert all(sgn(p[i][o])>=0 for i in range(8) for o in range(8))
fs=[(0,0),(1,1),(0,1),(1,0)]
for g in it.product(range(4),repeat=3):
    s=(Fr(0),Fr(0))
    for i in range(8): oo=tuple(fs[g[t]][B3[i][t]] for t in range(3)); s=add(s,p[i][B3.index(oo)])
    assert s==(1,0)
print('(3b) p >= 0, columns sum to 1, and all 64 deterministic interventions give total probability exactly 1: VALID')
json.dump([[ [str(x[0]),str(x[1])] for x in row] for row in p],open('cex_p_exact.json','w'))
# (4) separating inequality: search the normaliz facets (integers) mapped exactly to p-coordinates
import gzip, numpy as np
PF=np.load('../../pfs744.npy').astype(int)          # [744, i, o]
Zc=np.load('../../../physics/facets/Z.npy').astype(int)
import flint
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n'); kk=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:')); nf=int(L[kk].split()[0])
Hm=np.array([list(map(int,L[kk+1+f].split())) for f in range(nf)])
# float pre-screen only to CHOOSE a facet: p-coordinates via min-norm lstsq (any solution works for screening)
A=np.c_[PF.reshape(744,-1),np.ones(744)].astype(float); T=np.linalg.lstsq(A,Zc.astype(float),rcond=None)[0]
pf_float=np.array([[float(x[0])+float(x[1])*2**.5 for x in row] for row in p])
vals=(np.r_[pf_float.reshape(-1),1]@T)@Hm[:,:37].T+Hm[:,37]; f=int(vals.argmin()); print('float pre-screen: most violated facet',f,vals[f])
h=Hm[f]; target=[int(Zc[n]@h[:37])+int(h[37]) for n in range(744)]      # exact facet value on each PF (integers)
# exact rational g (65) with A g = target: rref of augmented matrix over Q
M=flint.fmpq_mat(744,66,[int(x) for row in np.c_[PF.reshape(744,-1),np.ones(744,int),np.array(target)] for x in row])
R,rk=M.rref(); g=[Fr(0)]*65
for r in range(rk):
    piv=next(c for c in range(66) if R[r,c]!=0); assert piv<65, 'inconsistent'
    g[piv]=Fr(int(R[r,65].p),int(R[r,65].q))
pfv=[sum(g[r]*int(PF.reshape(744,-1)[n][r]) for r in range(64))+g[64] for n in range(744)]
assert min(pfv)>=0; print('(4a) inequality valid on all 744 PFs exactly; tight on',sum(1 for x in pfv if x==0))
tot=(g[64],Fr(0))
for r in range(64):
    i,o=divmod(r,8); tot=add(tot,(g[r]*p[i][o][0],g[r]*p[i][o][1]))
print('(4b) g.p + g0 = %s + %s*sqrt2'%(tot[0],tot[1]),' sign',sgn(tot)); assert sgn(tot)<0
print('EXACT: purifiable (pure switchboard, source phi (x) |0>) valid classical process OUTSIDE conv(PF).')
print('g (p-coords, i-major):',[str(x) for x in g])
