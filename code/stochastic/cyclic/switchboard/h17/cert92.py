"""H.17.5' [EXACT]: orbit 92 holds on the whole valid polytope Valid.
Exact dual certificate: integer/rational y with r = g - Aeq^T y >= 0 componentwise and g0 + beq.y = 0 (checked in Fractions),
so g.p + g0 = r.p >= 0 for every p in Valid.  Also: the minimising face, its dimension, and whether it is a facet of Valid."""
import sys
src=open('validlp.py').read().split('\n# linear map')[0]
exec(src)
import sympy as sp
X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
f=int(np.nonzero(canon==92)[0][0]); h=Hm[f]; v=Zc@h[:37]+h[37]
g=np.linalg.lstsq(X.astype(float),v.astype(float),rcond=None)[0]
gq=[Fr(x).limit_denominator(10**4) for x in g]
assert all(sum(Fr(int(X[a,j]))*gq[j] for j in range(65))==int(v[a]) for a in range(744)), 'rationalised functional wrong'
gv=gq[:64]; g0=gq[64]
print('facet index',f,'range on PFs',max(v),'g0',g0)
# dual LP: max beq.y s.t. Aeq^T y <= g  (y free)
m=len(beq)
lp=linprog(-beq,A_ub=Aeq.T,b_ub=np.array([float(x) for x in gv]),bounds=[(None,None)]*m,method='highs')
print('dual LP',lp.status,-lp.fun+float(g0))
# rationalise on a basis: tight constraints of the dual -> solve exactly
y=lp.x
for den in [1,2,3,4,6,12,24,60,120,840]:
    yq=[Fr(round(t*den),den) for t in y]
    r=[gv[j]-sum(Fr(int(Aeq[i,j]))*yq[i] for i in range(m)) for j in range(64)]
    tot=g0+sum(Fr(beq[i]).limit_denominator(1)*yq[i] for i in range(m))
    if min(r)>=0 and tot>=0: break
else: 
    print('simple rationalisation failed; exact solve on tight set'); 
    T=[j for j in range(64) if abs(gv[j]-Aeq[:,j]@y)<1e-9]
    M=sp.Matrix([[int(Aeq[i,j]) for i in range(m)] for j in T]); rhs=sp.Matrix([sp.Rational(gv[j].numerator,gv[j].denominator) for j in T])
    sol,params=M.gauss_jordan_solve(rhs); sol=sol.subs({p:0 for p in params})
    yq=[Fr(int(sp.fraction(s)[0]),int(sp.fraction(s)[1])) for s in sol]
    r=[gv[j]-sum(Fr(int(Aeq[i,j]))*yq[i] for i in range(m)) for j in range(64)]
    tot=g0+sum(Fr(int(beq[i]))*yq[i] for i in range(m))
print('EXACT: min r =',min(r),' g0+b.y =',tot, ' => certificate', min(r)>=0 and tot>=0)
pos=[j for j in range(64) if r[j]>0]
print('y (nonzero):',{i:str(yq[i]) for i in range(m) if yq[i]!=0})
print('r>0 on',len(pos),'coordinates (i,o):',[(B3[j//8],B3[j%8],str(r[j])) for j in pos])
# minimising face F = Valid ∩ {p_j=0 : r_j>0} (exactly, when tot==0); its dimension
Js=[]  # coordinates forced to zero on F (numerical LP), beyond pos
Ab=[list(Aeq[i]) for i in range(m)]
for j in range(64):
    if j in pos: continue
    c=np.zeros(64); c[j]=-1
    l=linprog(c,A_eq=Aeq,b_eq=beq,bounds=[(0,0) if k in pos else (0,None) for k in range(64)],method='highs')
    if -l.fun<1e-9: Js.append(j)
Z=pos+Js
R=sp.Matrix(Ab+[[1 if k==j else 0 for k in range(64)] for j in Z]).rank()
dimF=64-R
RV=sp.Matrix(Ab).rank()
print('extra forced zeros',len(Js),'; dim Valid =',64-RV,'; dim F =',dimF,'; facet of Valid:',dimF==64-RV-1)
# Valid's own facets are p_j>=0 for non-forced j; check if F equals one of those
forced0=[j for j in range(64) if -linprog(np.eye(64)[j]*-1,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs').fun<1e-9]
print('coordinates identically 0 on Valid:',len(forced0))
print('coords zero on F but not on Valid:',[(B3[j//8],B3[j%8]) for j in sorted(set(Z)-set(forced0))])
# PFs on F
vals=[sum(int(PF.reshape(744,-1)[a,j])*r[j] for j in range(64)) for a in range(744)]
print('PFs on the face (r.p=0):',sum(1 for x in vals if x==0),'of 744')
