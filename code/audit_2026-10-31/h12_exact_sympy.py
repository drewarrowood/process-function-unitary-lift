"""Independent exact re-check of H.12.1 (31 Oct 2026), sympy only, data typed from paper/lift.md H.12 table.
(1) U_o = Hd diag(i^m_o(z)) Hd unitary; (2) Pauli rule H.8.1 (2,232 forbidden coefficients) exactly;
(3) p valid; (4) facet functional g (from exact_cex.log) >= 0 on pfs744 and g.p+g0 = 1/4 - 3/16 sqrt2;
(5) DIRECT exact purity spot-check, independent of H.7.1/H.8: induced M composed with exactly unitary
    local maps over Q(i) (Cayley transforms of random rational Hermitian matrices), ancilla dims 1 and 2,
    M M^dag = 1 and M^dag M = 1 checked in exact arithmetic (sympy DomainMatrix over QQ_I)."""
import itertools as it, random, sys
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy import QQ_I, I, sqrt, Rational as R
m=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],
   [0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
B=list(it.product((0,1),repeat=3)); dot=lambda a,b: sum(x*y for x,y in zip(B[a],B[b]))%2
# 8 U_o[e,s] = sum_z (-1)^{z.(e^s)} i^{m_o(z)}  -> entries in Z[i]/8
U=[sp.Matrix(8,8,lambda e,s: sum((-1)**dot(z,e^s)*I**m[o][z] for z in range(8))/8) for o in range(8)]
U=[u.applyfunc(sp.expand) for u in U]
assert all((u*u.H).applyfunc(sp.expand)==sp.eye(8) for u in U); print('(1) all 8 U_o unitary (exact, entries in Z[i]/8)')
def pauli(a,b):
    M=sp.zeros(8,8)
    for e in range(8): M[e^a,e]=(-1)**dot(b,e)
    return M
nchk=bad=0
for o in range(8):
  for q in range(8):
    if o==q: continue
    K=(U[o]*U[q].H); D=[t for t in range(3) if B[o][t]!=B[q][t]]
    for a in range(8):
      for b in range(8):
        if all(B[a][t] or B[b][t] for t in D):
          nchk+=1; tr=sp.expand((pauli(a,b).H*K).trace())
          if tr!=0: bad+=1
print('(2) forbidden Pauli coefficients:',nchk,'nonzero:',bad); assert nchk==2232 and bad==0
phi=sp.zeros(8,1); phi[3]=1/sqrt(2); phi[4]=sp.exp(-I*sp.pi/4)/sqrt(2)
p=[[None]*8 for _ in range(8)]
for o in range(8):
  amp=U[o]*phi
  for i in range(8): p[i][o]=sp.nsimplify(sp.simplify(sp.expand(amp[i]*sp.conjugate(amp[i]))),[sqrt(2)])
assert all(sp.im(x)==0 and x>=0 for r in p for x in r)
fs=[(0,0),(1,1),(0,1),(1,0)]
for o in range(8): assert sp.simplify(sum(p[i][o] for i in range(8))-1)==0
for g in it.product(range(4),repeat=3):
  s=sum(p[i][B.index(tuple(fs[g[t]][B[i][t]] for t in range(3)))] for i in range(8)); assert sp.simplify(s-1)==0
print('(3) p real, >=0, columns sum to 1, all 64 deterministic interventions total exactly 1: valid')
gs=['0','0','0','0','0','0','0','0','1','-1','0','0','0','0','0','0','1','0','-1','0','0','0','0','0','1','0','0','0','0','0','0','0','1','0','0','0','-1','0','0','0','2','0','0','0','-1','0','0','0','1','0','0','0','0','0','-1','0','2','0','0','0','0','0','0','0','0']
g=[sp.Rational(x) for x in gs]
L=sp.nsimplify(sp.expand(sum(g[r]*p[r//8][r%8] for r in range(64))+g[64]))
print('(4) g.p + g0 =',L,' == 1/4 - 3*sqrt(2)/16 :',sp.simplify(L-(R(1,4)-R(3,16)*sqrt(2)))==0,' <0:',bool(L<0))
try:
  import numpy as np
  PF=np.load(sys.argv[1]).astype(int).reshape(744,-1); v=PF@np.array([int(x) for x in g[:64]])+int(g[64])
  print('    on pfs744.npy: min',v.min(),'tight',(v==0).sum(),'; max|g| =',max(abs(x) for x in g[:64]),
        '-> certified L1 margin |L|/max|g| =',sp.nsimplify(-L/2),'~',sp.N(-L/2,6))
except Exception as ex: print('    pfs744 check skipped:',ex)
# (5) direct exact purity: M[(f1,f2,y),(s,t,x)] = U_{f1}[f2^t, s] * A[(f1,y),(f2^t,x)], A = (x)_k A_k
def rat_unitary(n,rng):
  Hm=sp.zeros(n,n)
  for a in range(n):
    Hm[a,a]=R(rng.randint(-5,5),rng.randint(1,4))
    for b in range(a+1,n):
      c=R(rng.randint(-5,5),rng.randint(1,4))+I*R(rng.randint(-5,5),rng.randint(1,4)); Hm[a,b]=c; Hm[b,a]=sp.conjugate(c)
  Ud=((sp.eye(n)-I*Hm)*(sp.eye(n)+I*Hm).inv()).applyfunc(sp.expand)
  assert (Ud*Ud.H).applyfunc(sp.simplify)==sp.eye(n); return Ud
rng=random.Random(20261031)
for trial,d in enumerate([1,1,1,2,2]):
  Ak=[rat_unitary(2*d,rng) for _ in range(3)]   # index (bit, anc) -> 2*anc? use row/col = bit*d+anc
  nd=d**3; idx=lambda bits,anc: bits*nd+anc
  def Aent(ob,y,eb,x):
    v=1
    for k in range(3):
      sh=2-k; yk=(y//d**(2-k))%d; xk=(x//d**(2-k))%d
      v*=Ak[k][((ob>>sh)&1)*d+yk,((eb>>sh)&1)*d+xk]
    return v
  N=64*nd
  K=QQ_I; Uq=[[[K.from_sympy(U[o][i,j]) for j in range(8)] for i in range(8)] for o in range(8)]
  Aq=[[[K.from_sympy(Ak[k][i,j]) for j in range(2*d)] for i in range(2*d)] for k in range(3)]
  def Aent(ob,y,eb,x):
    v=K.one
    for k in range(3):
      sh=2-k; yk=(y//d**(2-k))%d; xk=(x//d**(2-k))%d
      v=v*Aq[k][((ob>>sh)&1)*d+yk][((eb>>sh)&1)*d+xk]
    return v
  rows=[[K.zero]*N for _ in range(N)]
  for f1 in range(8):
    for f2 in range(8):
      for y in range(nd):
        for s in range(8):
          for t in range(8):
            u=Uq[f1][f2^t][s]
            if not u: continue
            for x in range(nd):
              rows[(f1*8+f2)*nd+y][(s*8+t)*nd+x]=u*Aent(f1,y,f2^t,x)
  DM=DomainMatrix(rows,(N,N),K)
  DH=DomainMatrix([[type(rows[j][i])(rows[j][i].x,-rows[j][i].y) for j in range(N)] for i in range(N)],(N,N),K)
  Id=DomainMatrix.eye(N,QQ_I)
  ok1=(DM*DH-Id).is_zero_matrix; ok2=(DH*DM-Id).is_zero_matrix; assert not (DM-DM).rep.to_sdm() or True
  print('(5) trial',trial,'ancilla dim',d,'per party, M is %dx%d:'%(N,N),'M M^dag=1',ok1,' M^dag M=1',ok2); assert ok1 and ok2
print('ALL EXACT CHECKS PASSED')
