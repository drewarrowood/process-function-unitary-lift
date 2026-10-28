"""Round 29: a stronger Hermitian SOS relaxation of the reduced family (H.31.1), exported in the h27_export.py JSON format so that
h27_face.py solves it unchanged.  Independent of h26_hsos.poly: p is rebuilt here symbolically from its definition
    p(psi,xi,u) = sum_{i,o} T[i,o] |<f_i(xi)| D_o(u) psi>|^2 + c |psi|^2 prod_k |xi_k|^2,
    f_i = (x)_k e_{i_k},  e_0 = xi_k,  e_1 = (-conj xi_k1, conj xi_k0),  D_o(u) psi_w = prod_k u_k^{o_k X[w][k]} psi_w   (|u_k| = 1),
as a polynomial in psi, conj psi, xi, conj xi (exponent vectors) and a Laurent polynomial in u.
Level K (env K = party 0/1/2, or unset = level 0): prove  |xi_K|^2 (p - gamma |psi|^2 prod|xi_k|^2) = sum_blocks v^dag Q v,  Q >= 0.
v entries: psi_w * prod_k phi_k * u^m, with phi_k one of xi_kb ('h') or conj xi_kb ('c') for k != K and, for k = K, one of
xi_Ka xi_Kb ('hh', a<=b), xi_Ka conj xi_Kb ('hc') or conj xi_Ka conj xi_Kb ('cc');  m in {0..X[w][k]} (default) or {0,1}^3 (MB=full).
Each pattern is its own Gram family, split further by torus weight (the symmetry of H.34.1, asserted on every coefficient).
On the unit spheres |xi_K| = 1, so any feasible gamma is a lower bound on the facet value.  Level 0 (K unset) reproduces H.33.1.
JSON also lists every basis monomial (mono: [psi, psibar, xi, xibar, u-exponents]) for h29_zs.py and the h29 checkers.
usage: orbit out.json"""
import sys, os, json, itertools as it, numpy as np
from fractions import Fraction as F
from h20_common import Tn, canon, B3
from h26_hsos import X
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0])
T=np.array([[F(x).limit_denominator(10**4) for x in row] for row in Tn[f,:64].reshape(8,8)],dtype=object); c=F(Tn[f,64]).limit_denominator(10**4)
assert max(abs(float(T[i,j])-Tn[f,8*i+j]) for i in range(8) for j in range(8))<1e-13 and abs(float(c)-Tn[f,64])<1e-13
K=os.environ.get('K'); KS=[int(x) for x in K.split(',')] if K not in (None,'') else []   # K=0,1,2: multiplier sum_K |xi_K|^2, union of the patterns
K=KS[0] if KS else None
# monomial: (psi 8, psibar 8, xi 6, xibar 6, d 3) exponent tuples; xi index 2k+b
Z8=(0,)*8; Z6=(0,)*6
def mono(psi=None,psib=None,xi=(),xib=(),d=(0,0,0)):
    a=[0]*8; ab=[0]*8; x=[0]*6; xb=[0]*6
    if psi is not None: a[psi]+=1
    if psib is not None: ab[psib]+=1
    for j in xi: x[j]+=1
    for j in xib: xb[j]+=1
    return (tuple(a),tuple(ab),tuple(x),tuple(xb),tuple(d))
def mul(m1,m2): return tuple(tuple(p+q for p,q in zip(a,b)) for a,b in zip(m1,m2))
def pmul(P,Q):
    R={}
    for a,x in P.items():
        for b,y in Q.items():
            k=mul(a,b); R[k]=R.get(k,0)+x*y
    return {k:v for k,v in R.items() if v!=0}
def padd(P,Q,s=1):
    R=dict(P)
    for k,v in Q.items(): R[k]=R.get(k,0)+s*v
    return {k:v for k,v in R.items() if v!=0}
def conjm(m): return (m[1],m[0],m[3],m[2],tuple(-x for x in m[4]))
def conjp(P): return {conjm(k):v for k,v in P.items()}   # coefficients are real here
def econj(k,ik,b):   # conj(e_{ik}[b]) for party k as a polynomial
    if ik==0: return {mono(xib=(2*k+b,)):F(1)}
    return {mono(xi=(2*k+1,)):F(-1)} if b==0 else {mono(xi=(2*k,)):F(1)}
P={}
for i in range(8):
    for o in range(8):
        if T[i,o]==0: continue
        A={}
        for w in range(8):
            term={mono(psi=w,d=tuple(B3[o][k]*X[w][k] for k in range(3))):F(1)}
            for k in range(3): term=pmul(term,econj(k,B3[i][k],B3[w][k]))
            A=padd(A,term)
        P=padd(P,{k:v*T[i,o] for k,v in pmul(conjp(A),A).items()})
nsq={}
for w in range(8): nsq=padd(nsq,{mono(psi=w,psib=w):F(1)})
for k in range(3): nsq=pmul(nsq,{mono(xi=(2*k,),xib=(2*k,)):F(1),mono(xi=(2*k+1,),xib=(2*k+1,)):F(1)})
P=padd(P,{k:v*c for k,v in nsq.items()})
if KS:
    mK={}
    for k_ in KS: mK=padd(mK,{mono(xi=(2*k_,),xib=(2*k_,)):F(1),mono(xi=(2*k_+1,),xib=(2*k_+1,)):F(1)})
    P=pmul(P,mK); NV=pmul(nsq,mK)
else: NV=nsq
def wt(m):   # torus weight: psi_w -> e^{i phi.w}, xi_k1 -> e^{i phi_k} xi_k1
    return tuple(sum(B3[w][k]*(m[0][w]-m[1][w]) for w in range(8))+m[2][2*k+1]-m[3][2*k+1] for k in range(3))
assert all(wt(m)==(0,0,0) for m in list(P)+list(NV)), 'torus symmetry fails'
assert all(conjm(m) in P and P[conjm(m)]==v for m,v in P.items()), 'p not real'
# basis
full=os.environ.get('MB','')=='full'
blocks=[]; vm=[]
for K in (KS or [None]):
  pats=[]
  for k in range(3):
    if k==K: pats.append([('hh',[(a,b) for a in (0,1) for b in (0,1) if a<=b]),('hc',[(a,b) for a in (0,1) for b in (0,1)]),('cc',[(a,b) for a in (0,1) for b in (0,1) if a<=b])])
    else: pats.append([('h',[(a,) for a in (0,1)]),('c',[(a,) for a in (0,1)])])
  for pat in it.product(*pats):
    name=''.join(p[0]+'.' for p in pat); cls={}
    for w in range(8):
        ms=list(it.product((0,1),repeat=3)) if full else list(it.product(*[range(X[w][k]+1) for k in range(3)]))
        for choice in it.product(*[p[1] for p in pat]):
            xi=[];xib=[]
            for k,(pn,ch) in enumerate(zip([p[0] for p in pat],choice)):
                for t,ch_ in zip(pn,ch): (xi if t=='h' else xib).append(2*k+ch_)
            for m in ms:
                mm=mono(psi=w,xi=xi,xib=xib,d=m); cls.setdefault(wt(mm),[]).append(len(vm)); vm.append(mm)
    for wv,ids in sorted(cls.items()): blocks.append(dict(S=name,wt=list(wv),basis=ids))
ent={}
for bi,bl in enumerate(blocks):
    for r,ir in enumerate(bl['basis']):
        for s,is_ in enumerate(bl['basis']):
            ent.setdefault(mul(conjm(vm[ir]),vm[is_]),[]).append((bi,r,s))
miss=[k for k in P if k not in ent]; assert not miss, ('uncovered key',miss[:3])
rows=[]
for k in ent:
    kc=conjm(k)
    if kc<k: continue
    rows.append(dict(part='re',rhs=str(F(P.get(k,0))),nv=str(F(NV.get(k,0))),terms=[[bi,r,s] for bi,r,s in ent[k]]))
    if kc!=k: rows.append(dict(part='im',rhs='0',nv='0',terms=[[bi,r,s] for bi,r,s in ent[k]]))
json.dump(dict(orbit=orb,facet=f,level=('K='+','.join(map(str,KS)) if KS else '0'),mb=('full' if full else 'default'),blocks=blocks,rows=rows,mono=[[list(x) for x in m] for m in vm]),open(sys.argv[2],'w'))
sz=[len(b['basis']) for b in blocks]
print(f'orbit {orb} facet {f} level {KS or 0}: {len(blocks)} blocks, sizes max {max(sz)} sum {sum(sz)} sum n^2 {sum(x*x for x in sz)}; rows {len(rows)}; keys of p {len(P)}')
