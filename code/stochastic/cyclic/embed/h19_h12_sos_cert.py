"""Round 19 (H.26.2): exact SOS certificate that min f_O >= lambda_cert on (S^2)^6 for an output pattern O (default 21 = the
H.25.2 optimum's pattern), from the level-2 dual:  f_O - lambda = s0 + sum_i h_i (|n_i|^2 - 1),  s0 = m^T G m (m = 190 monomials of
degree <= 2), G >= eps*1.  Steps: (1) SCS solves the dual with G - eps*1 PSD; (2) the coefficients of f_O (in Q(sqrt2), computed
at 60 digits) are rounded to rationals f_q with |f_O - f_q| <= errsum on (S^2)^6 (every monomial has modulus <= 1 there);
(3) G and h are rounded to rationals and the coefficient residual is moved exactly into G (one entry pair per monomial);
(4) G - (eps/4)*1 is checked PSD exactly (fraction-free Bareiss LDL on integers: all pivots > 0).  Then on (S^2)^6
f_O >= f_q - errsum = lambda + s0 - errsum >= lambda - errsum.   [EXACT-CERTIFIED]
Usage: h19_h12_sos_cert.py [pattern] [eps] [scs_eps] [max_iters]"""
import sys, itertools as it, numpy as np, cvxpy as cp, scipy.sparse as sp
from fractions import Fraction as Fr
pat=int(sys.argv[1]) if len(sys.argv)>1 else 21; eps=float(sys.argv[2]) if len(sys.argv)>2 else 1e-6
src=open('h18_h12_local.py').read(); src=src[:src.index("E=np.load")]; argv=sys.argv; sys.argv=[argv[0]]; exec(src); sys.argv=argv
import mpmath as mp
dd={}
for xi,x in enumerate(B3):
    for Ssub in it.product((0,1),repeat=3):
        dd[x,Ssub]=Fr(sum(int(y[xi,ai])*(-1)**sum(a[k] for k in range(3) if Ssub[k]) for ai,a in enumerate(B3)),8)
VAR=[(k,x,c) for k in range(3) for x in range(2) for c in range(3)]; vi={v:i for i,v in enumerate(VAR)}; nv=18
pats=list(it.product((0,1),repeat=6)); O=[[pats[pat][2*k],pats[pat][2*k+1]] for k in range(3)]
P={}
for x in B3:
    ox=B3.index(tuple(int(O[k][x[k]]) for k in range(3)))
    for mu in MU:
        q=dd[x,tuple(int(m>0) for m in mu)]
        if q==0: continue
        key=tuple(sorted(vi[(k,x[k],mu[k]-1)] for k in range(3) if mu[k])); P[key]=P.get(key,0)+t[ox,mu]*mp.mpf(q.numerator)/q.denominator
Q=10**30; Pq={k:Fr(int(mp.nint(v*Q)),Q) for k,v in P.items()}
errsum=sum(abs(v-mp.mpf(Pq[k].numerator)/Pq[k].denominator) for k,v in P.items())
print('pattern',pat,O,'; monomials in f:',len(P),'; rounding error bound errsum =',mp.nstr(errsum,5),flush=True)
mons2=[()]+[(i,) for i in range(nv)]+[(i,j) for i in range(nv) for j in range(i,nv)]; L=len(mons2)
allm={}
def mid(m):
    m=tuple(sorted(m))
    if m not in allm: allm[m]=len(allm)
    return allm[m]
for a in mons2:
    for b in mons2: mid(a+b)
nm=len(allm)
SPH=[[vi[(k,x,c)] for c in range(3)] for k in range(3) for x in range(2)]
# linear map: coefficient vector of  m^T G m + sum_i h_i (|n_i|^2-1)
Gi=np.array([[allm[tuple(sorted(a+b))] for b in mons2] for a in mons2]).ravel()
AG=sp.csr_matrix((np.ones(L*L),(Gi,np.arange(L*L))),shape=(nm,L*L))
rows=[];cols=[];vals=[]
for si,q in enumerate(SPH):
    for j,m in enumerate(mons2):
        col=si*L+j
        for i in q: rows.append(allm[tuple(sorted(m+(i,i)))]); cols.append(col); vals.append(1.0)
        rows.append(allm[tuple(sorted(m))]); cols.append(col); vals.append(-1.0)
AH=sp.csr_matrix((vals,(rows,cols)),shape=(nm,6*L))
fv=np.zeros(nm)
for k,v in P.items(): fv[allm[k]]+=float(v)
G=cp.Variable((L,L),symmetric=True); h=cp.Variable(6*L); lam=cp.Variable()
e0=np.zeros(nm); e0[allm[()]]=1
pr=cp.Problem(cp.Maximize(lam),[AG@cp.vec(G,order='C')+AH@h+lam*e0==fv, G-eps*np.eye(L)>>0])
pr.solve(solver='SCS',eps=float(sys.argv[3]) if len(sys.argv)>3 else 1e-9,max_iters=int(sys.argv[4]) if len(sys.argv)>4 else 100000)
print('SCS:',pr.status,'lambda =',lam.value,flush=True)
D=2**40
rnd=lambda v:Fr(int(round(v*D)),D)
lamq=Fr(int(np.floor(lam.value*10**7)),10**7)          # rational lambda, rounded down
Gq=[[rnd((G.value[a,b]+G.value[b,a])/2) for b in range(L)] for a in range(L)]
hq=[rnd(v) for v in h.value]
# exact residual
res={m:Fr(0) for m in range(nm)}
for k,v in Pq.items(): res[allm[k]]+=v
res[allm[()]]-=lamq
for a in range(L):
    for b in range(L): res[Gi[a*L+b]]-=Gq[a][b]
AHc=AH.tocoo()
for r_,c_,v_ in zip(AHc.row,AHc.col,AHc.data): res[r_]-=int(v_)*hq[c_]
# move residual into G: for monomial m pick the first pair (a,b) with a<=b, m_a+m_b=m
pair={}
for a in range(L):
    for b in range(a,L): pair.setdefault(Gi[a*L+b],(a,b))
maxr=max(abs(v) for v in res.values()); print('max exact residual before repair:',float(maxr),flush=True)
for m,v in res.items():
    if v==0: continue
    a,b=pair[m]
    if a==b: Gq[a][a]+=v
    else: Gq[a][b]+=v/2; Gq[b][a]+=v/2
# re-check identity exactly
chk={m:Fr(0) for m in range(nm)}
for a in range(L):
    for b in range(L): chk[Gi[a*L+b]]+=Gq[a][b]
for r_,c_,v_ in zip(AHc.row,AHc.col,AHc.data): chk[r_]+=int(v_)*hq[c_]
chk[allm[()]]+=lamq
fqv={m:Fr(0) for m in range(nm)}
for k,v in Pq.items(): fqv[allm[k]]+=v
print('identity f_q = lambda + m^T G m + sum h_i(|n_i|^2-1) holds exactly:',chk==fqv,flush=True)
# exact PSD test of G - (eps/4) 1 via fraction-free LDL (Bareiss) on integers
den=1
for row in Gq:
    for v in row: den=den*v.denominator//np.gcd(den,v.denominator) if False else (den*v.denominator)//__import__('math').gcd(den,v.denominator)
sh=Fr(eps).limit_denominator(10**12)/4
Mint=[[int((Gq[a][b]-(sh if a==b else 0))*den*sh.denominator) for b in range(L)] for a in range(L)]
def bareiss_pd(A):
    A=[r[:] for r in A]; n=len(A); prev=1
    for k in range(n):
        if A[k][k]<=0: return False,k
        for i in range(k+1,n):
            for j in range(k+1,n): A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])//prev
        prev=A[k][k]
    return True,n
ok,kk=bareiss_pd(Mint); print('G - (eps/4)*1 positive definite (exact Sylvester/Bareiss):',ok,kk,flush=True)
if ok and chk==fqv:
    lb=mp.mpf(lamq.numerator)/lamq.denominator-errsum
    print(f'CERTIFIED: for output pattern {pat}, min over (S^2)^6 of f_O >= {lamq} - errsum >= {mp.nstr(lb,15)}')
