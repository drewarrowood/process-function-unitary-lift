"""Round 27 (H.34.1): export the Round-26 Hermitian decomposable SOS problem (h26_hsos.py) in symmetry-reduced form for Clarabel.jl.
Torus symmetry: p is invariant under xi_{k1} -> e^{i phi_k} xi_{k1}, psi_z -> e^{i phi_k z_k} psi_z (checked below on every
coefficient).  So each Gram block Q_S may be taken block-diagonal by torus weight (Reynolds average), wt_k(w,b) = w_k + b_k (k notin S)
or w_k - b_k (k in S).  Each complex key equality is kept once per conjugate pair (real part; imaginary part unless self-conjugate).
Coefficients are exact rationals.  Output JSON: blocks [{S, wt, basis}], rows [{re/im, rhs "p/q", nv "p/q", terms [[blk, r, s, part]]}]
where part: Q[r,s] = X11+X22 + i(X21-X12) of the real 2n x 2n PSD X.  usage: orbit out.json"""
import sys, json, numpy as np
from fractions import Fraction as F
import h26_hsos as H
orb=int(sys.argv[1]); f=int(np.where(H.canon==orb)[0][0])
T=np.array([[F(x).limit_denominator(10**4) for x in row] for row in H.Tn[f,:64].reshape(8,8)],dtype=object); c=F(H.Tn[f,64]).limit_denominator(10**4)
assert max(abs(float(T[i,j])-H.Tn[f,8*i+j]) for i in range(8) for j in range(8))<1e-13
P,N=H.poly(T,c); P={k:v for k,v in P.items() if v!=0}
wkey=lambda k: tuple(-H.B3[k[0]][j]+H.B3[k[1]][j]+k[2][j]-k[3][j] for j in range(3))
assert all(wkey(k)==(0,0,0) for k in list(P)+list(N)), 'torus symmetry fails'
B=H.basis(); blocks=[]
for S in range(8):
    cls={}
    for idx,(w,b,m) in enumerate(B):
        wt=tuple(H.B3[w][k]+(-1 if (S>>k)&1 else 1)*H.B3[b][k] for k in range(3)); cls.setdefault(wt,[]).append(idx)
    for wt,ids in sorted(cls.items()): blocks.append(dict(S=S,wt=wt,basis=ids))
def key(S,r,s):
    (z,a,m),(w,b,mp)=B[r],B[s]; xi=[];xb=[]
    for k in range(3):
        ak,bk=H.B3[a][k],H.B3[b][k]
        if (S>>k)&1: xi.append(ak); xb.append(bk)
        else: xi.append(bk); xb.append(ak)
    return (z,w,tuple(xi),tuple(xb),tuple(mp[k]-m[k] for k in range(3)))
conjk=lambda k:(k[1],k[0],k[3],k[2],tuple(-x for x in k[4]))
ent={}
for bi,bl in enumerate(blocks):
    for r,ir in enumerate(bl['basis']):
        for s,is_ in enumerate(bl['basis']):
            ent.setdefault(key(bl['S'],ir,is_),[]).append((bi,r,s))
for k in P: assert k in ent, ('uncovered key',k)
rows=[]
for k in ent:
    kc=conjk(k)
    if kc<k: continue
    b=F(P.get(k,0)); nv=F(N.get(k,0))
    rows.append(dict(part='re',rhs=str(b),nv=str(nv),terms=[[bi,r,s] for bi,r,s in ent[k]]))
    if kc!=k: rows.append(dict(part='im',rhs='0',nv='0',terms=[[bi,r,s] for bi,r,s in ent[k]]))
json.dump(dict(orbit=orb,facet=f,blocks=[dict(S=b['S'],wt=list(b['wt']),basis=b['basis']) for b in blocks],rows=rows),open(sys.argv[2],'w'))
sz=[len(b['basis']) for b in blocks]
print(f'orbit {orb} facet {f}: {len(blocks)} blocks, sizes max {max(sz)} sum {sum(sz)} sum n^2 {sum(x*x for x in sz)}; rows {len(rows)} (full problem: 8 x {len(B)})')
