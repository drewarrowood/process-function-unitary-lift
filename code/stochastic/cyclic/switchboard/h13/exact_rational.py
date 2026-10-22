"""H.13.2 EXACT (rational arithmetic only): a REAL, RATIONAL purifiable classical process outside conv(PF).
Board U_o = Hd diag((-1)^{m_o(z)/2}) Hd (real orthogonal, entries in (1/4)Z), phases from min_cex.json;
source phi = (|0>+|1>+|2>-|5>)/2 (also tests (|0>+|1>+|2>)/sqrt3).  Checks: orthogonality, Pauli rule H.8.1
(=> pure with/without ancillas by H.8.1-H.8.2), validity, and an exact facet inequality violated."""
import json, itertools as it, gzip, numpy as np, flint
from fractions import Fraction as Fr
B3=list(it.product((0,1),repeat=3)); d=json.load(open('min_cex.json')); m=d['m']
H=[[Fr((-1)**(sum(a*b for a,b in zip(x,y))%2)) for y in B3] for x in B3]   # sqrt8*Hd
mm=lambda A,B:[[sum(A[i][l]*B[l][j] for l in range(8)) for j in range(8)] for i in range(8)]
tr=lambda A:[list(r) for r in zip(*A)]
U=[[[x/8 for x in r] for r in mm(mm(H,[[Fr((-1)**(m[o][x]//2)) if x==y else Fr(0) for y in range(8)] for x in range(8)]),H)] for o in range(8)]
I=[[Fr(int(i==j)) for j in range(8)] for i in range(8)]
assert all(mm(U[o],tr(U[o]))==I for o in range(8)); print('(1) all U_o real orthogonal, entries in Z/4: exact')
def pauli(a,b):
    M=[[0]*8 for _ in range(8)]
    for e,eb in enumerate(B3): M[B3.index(tuple(x^y for x,y in zip(eb,a)))][e]=(-1)**sum(p*q for p,q in zip(b,eb))
    return M
P={(a,b):pauli(a,b) for a in B3 for b in B3}; bad=n=0
for o in range(8):
    for q in range(8):
        if o==q: continue
        K=mm(U[o],tr(U[q])); D=[t for t in range(3) if B3[o][t]!=B3[q][t]]
        for (a,b),S in P.items():
            if all(a[t] or b[t] for t in D):
                n+=1; bad+= sum(S[j][i]*K[j][i] for i in range(8) for j in range(8))!=0
print('(2) forbidden Pauli coefficients checked',n,'nonzero',bad); assert bad==0
pts=[np.array(B3,int)]
PF=np.load('../../pfs744.npy').astype(int); Zc=np.load('../../../physics/facets/Z.npy').astype(int)
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
def facet_g(f):
    h=list(map(int,L[k+1+f].split())); target=[int(Zc[r]@np.array(h[:37]))+h[37] for r in range(744)]
    M=flint.fmpq_mat(744,66,[int(x) for row in np.c_[PF.reshape(744,-1),np.ones(744,int),np.array(target)] for x in row])
    R,rk=M.rref(); g=[Fr(0)]*65
    for r in range(rk):
        piv=next(c for c in range(66) if R[r,c]!=0); assert piv<65; g[piv]=Fr(int(R[r,65].p),int(R[r,65].q))
    pv=[sum(g[r]*int(PF.reshape(744,-1)[t][r]) for r in range(64))+g[64] for t in range(744)]
    assert min(pv)==0; return g,max(pv),sum(x==0 for x in pv)
for name,phi in [('(|0>+|1>+|2>-|5>)/2',[Fr(1,2)]*3+[0,0,Fr(-1,2),0,0]),('(|0>+|1>+|2>)/sqrt3 [p uses phi phi^T]',None)]:
    if phi is None: amp2=lambda o,i:(U[o][i][0]+U[o][i][1]+U[o][i][2])**2/3
    else: amp2=lambda o,i,phi=phi:sum(U[o][i][s]*phi[s] for s in range(8))**2
    p=[[amp2(o,i) for o in range(8)] for i in range(8)]
    assert all(sum(p[i][o] for i in range(8))==1 for o in range(8))
    fs=[(0,0),(1,1),(0,1),(1,0)]
    for gg in it.product(range(4),repeat=3):
        assert sum(p[i][B3.index(tuple(fs[gg[t]][B3[i][t]] for t in range(3)))] for i in range(8))==1
    best=None
    for f in [d['facet'],16962,15629]:
        g,rng,nt=facet_g(f); val=sum(g[r]*p[r//8][r%8] for r in range(64))+g[64]
        print('   facet',f,'tight on',nt,'PFs, range',rng,': value on p =',val,'(relative %.4f)'%float(val/rng))
        if val<0: best=f
    assert best is not None
    print('(3,4)',name,': p rational, VALID, OUTSIDE conv(PF)  p =',[[str(x) for x in r] for r in p] if phi else '')
