"""Round 21 (H.28.1): INDEPENDENT exact check of a phase-board crossing (code path disjoint from h21_trev_cert.py).
The board, in qubit form: V |t>_AO |f>_P = z(t,f) |f>_AI |t>_F, z(t,f) = prod_k z_k(t_k, w'_k(f_{-k})), |z_k| = 1 exactly
(z = (1+iq)/(1-iq), q = tan(theta/2) rounded to a rational), followed by exact Cayley-rational SU(2)-type frames E_k^T on AI.
Checks, all in exact rational arithmetic (complex numbers as pairs of Fractions in numpy object arrays):
 (1) V'^dag V' = 1;  (2) the Araujo et al. validity projector residual of W = Tr_F |V'>><<V'| is exactly 0 (all 3^3 trace-and-replace
 terms, as in h16_gen_search.penalty) and Tr W = d_O d_P = 64;  (3) p(i|o) = <psi|forms|psi>/<psi|psi> exact, valid (64 interventions);
 (4) exact facet value (functional fitted to the 744 PF values and checked exactly).  Then (5) the 384-element group (party
 permutations x input flips x output flips) is applied to p and the violated facets of each open orbit are counted (float).
usage: phase.npy W ORB [DEN]"""
import sys, json, itertools as it, numpy as np
from fractions import Fraction as Fr
ph=np.load(sys.argv[1]); W=int(sys.argv[2]); ORB=int(sys.argv[3]); DEN=int(sys.argv[4]) if len(sys.argv)>4 else 10**6
sys.path.insert(0,'.'); from h20_common import B3, Tn, canon, OPEN, REP, others, valsI, PF
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]; parts=maxi[W]; nb=[max(p)+1 for p in parts]
q=lambda x:Fr(round(float(x)*DEN),DEN)
class C:   # exact Gaussian rational
    __slots__=('r','i')
    def __init__(s,r,i=Fr(0)): s.r=Fr(r); s.i=Fr(i)
    def __add__(s,o): o=o if isinstance(o,C) else C(o); return C(s.r+o.r,s.i+o.i)
    __radd__=__add__
    def __sub__(s,o): o=o if isinstance(o,C) else C(o); return C(s.r-o.r,s.i-o.i)
    def __mul__(s,o): o=o if isinstance(o,C) else C(o); return C(s.r*o.r-s.i*o.i,s.r*o.i+s.i*o.r)
    __rmul__=__mul__
    def __truediv__(s,o):
        o=o if isinstance(o,C) else C(o); n=o.r*o.r+o.i*o.i; return C((s.r*o.r+s.i*o.i)/n,(s.i*o.r-s.r*o.i)/n)
    def conj(s): return C(s.r,-s.i)
    def __eq__(s,o): o=o if isinstance(o,C) else C(o); return s.r==o.r and s.i==o.i
    def __float__(s): return float(s.r)
    def cx(s): return complex(float(s.r),float(s.i))
ONE=C(1); ZERO=C(0); Iu=C(0,1)
def zphase(th): t=q(np.tan(th/2)); return (ONE+Iu*t)/(ONE-Iu*t)
def su2(t):
    a,b,c=t; return np.array([[np.cos(a)*np.exp(1j*b), -np.sin(a)*np.exp(-1j*c)],[np.sin(a)*np.exp(1j*c), np.cos(a)*np.exp(-1j*b)]])
def cayley2(U):
    best=None
    for w in (ONE,Iu,C(-1),C(0,-1)):
        V=np.conj(w.cx())*U; m=np.abs(np.linalg.eigvals(V)+1).min()
        if best is None or m>best[0]: best=(m,w,V)
    _,w,V=best; K=1j*(np.eye(2)-V)@np.linalg.inv(np.eye(2)+V); K=(K+K.conj().T)/2
    Kq=[[C(q(K[0,0].real)),C(q(K[0,1].real),q(K[0,1].imag))],[None,C(q(K[1,1].real))]]; Kq[1][0]=Kq[0][1].conj()
    A=[[(ONE if i==j else ZERO)+Iu*Kq[i][j] for j in range(2)] for i in range(2)]
    B=[[(ONE if i==j else ZERO)-Iu*Kq[i][j] for j in range(2)] for i in range(2)]
    det=B[0][0]*B[1][1]-B[0][1]*B[1][0]; Bi=[[B[1][1]/det,(ZERO-B[0][1])/det],[(ZERO-B[1][0])/det,B[0][0]/det]]
    return [[w*(A[i][0]*Bi[0][j]+A[i][1]*Bi[1][j]) for j in range(2)] for i in range(2)]
off=0; z=[]; Ex=[]
for k in range(3):
    t=ph[off:off+2*nb[k]].reshape(2,nb[k]); off+=2*nb[k]; z.append([[zphase(t[o,x]) for x in range(nb[k])] for o in range(2)])
for k in range(3): Ex.append(cayley2(su2(ph[off:off+3]))); off+=3
psi=ph[off:off+8]+1j*ph[off+8:off+16]
for k in range(3):
    U=Ex[k]; P=[[sum((U[l][i].conj()*U[l][j] for l in range(2)),ZERO) for j in range(2)] for i in range(2)]
    assert all(P[i][j]==(ONE if i==j else ZERO) for i in range(2) for j in range(2))
    for o in range(2):
        for x in range(nb[k]): assert z[k][o][x]*z[k][o][x].conj()==ONE
print('phases have modulus exactly 1; frames exactly unitary')
# V'[(i,s),(t,f)] = [s==t] * prod_k ET_k[i_k, f_k] * z(t,f)     (rows 8*i+s, cols 8*t+f)
zt=[[None]*8 for _ in range(8)]
for t_ in range(8):
    for f in range(8):
        v=ONE
        for k in range(3): v=v*z[k][B3[t_][k]][parts[k][others(k,f)]]
        zt[t_][f]=v
ET=[[[Ex[k][a][i] for a in range(2)] for i in range(2)] for k in range(3)]   # ET[k][i][a] = E_k[a,i]
def etp(i,f):
    v=ONE
    for k in range(3): v=v*ET[k][B3[i][k]][B3[f][k]]
    return v
Vx=np.empty((64,64),dtype=object)
for i in range(8):
    for s in range(8):
        for t_ in range(8):
            for f in range(8): Vx[8*i+s,8*t_+f]=etp(i,f)*zt[t_][f] if s==t_ else ZERO
# (1) unitarity
Vd=np.vectorize(lambda c:c.conj(),otypes=[object])(Vx).T
VV=Vd.dot(Vx); assert all(VV[a,b]==(ONE if a==b else ZERO) for a in range(64) for b in range(64)); print('(1) V\' exactly unitary (64x64)')
# (2) Araujo projector, exact.  Choi of Tr_F: indices (iA iB iC oA oB oC s) x primed
W4=Vx.reshape(2,2,2,8,2,2,2,8)   # i0 i1 i2 f(=F) o0 o1 o2 s(=P)
Wc=np.empty([2,2,2,2,2,2,8]*2,dtype=object)
Wc[...]=ZERO
idx=list(it.product(range(2),range(2),range(2),range(2),range(2),range(2),range(8)))
nz={}
for r in idx:
    a,b,c,x,y,zz,s=r
    col=[W4[a,b,c,F,x,y,zz,s] for F in range(8)]
    if any(not (e==ZERO) for e in col): nz[r]=col
keys=list(nz)
for r in keys:
    for r2 in keys:
        Wc[r+r2]=sum((nz[r][F]*nz[r2][F].conj() for F in range(8)),ZERO)
n=7
def tr_rep(Wm,axes):
    for a in axes:
        d=Wm.shape[a]
        t=np.trace(Wm,axis1=a,axis2=a+n) if False else None
        # trace over (a, a+n) keeping order
        sl=[ [slice(None)]*(2*n) for _ in range(d)]
        tot=None
        for j in range(d):
            ix=[slice(None)]*(2*n); ix[a]=j; ix[a+n]=j
            part=Wm[tuple(ix)]
            tot=part if tot is None else tot+part
        tot=np.expand_dims(tot,a); tot=np.expand_dims(tot,a+n)
        new=np.empty([d if j in (a,a+n) else Wm.shape[j] for j in range(2*n)],dtype=object); new[...]=ZERO
        for j in range(d):
            ix=[slice(None)]*(2*n); ix[a]=slice(j,j+1); ix[a+n]=slice(j,j+1)
            new[tuple(ix)]=tot*C(Fr(1,d))
        Wm=new
    return Wm
IN={0:0,1:1,2:2}; OUT={0:3,1:4,2:5}
tot=None
for ch in it.product(range(3),repeat=3):
    sgn=1; ax=[]
    for kk,c in enumerate(ch):
        if c==1: sgn=-sgn; ax.append(OUT[kk])
        if c==2: ax+=[IN[kk],OUT[kk]]
    term=tr_rep(Wc,ax); term=term if sgn>0 else term*C(-1)
    tot=term if tot is None else tot+term
Dm=tot-tr_rep(Wc,list(range(7)))
assert all(e==ZERO for e in Dm.flat); trW=sum((Wc[r+r] for r in idx),ZERO)
print('(2) Araujo validity projector residual exactly 0; Tr W =',trW.r)
# (3) p exact
ps=[C(q(x.real),q(x.imag)) for x in psi]; nn=sum((c*c.conj() for c in ps),ZERO).r
p=[[None]*8 for _ in range(8)]
for i in range(8):
    for t_ in range(8):
        tot=Fr(0)
        for s in range(8):
            amp=sum((Vx[8*i+s,8*t_+f]*ps[f] for f in range(8)),ZERO); tot+=(amp*amp.conj()).r
        p[i][t_]=tot/nn
assert all(x>=0 for r in p for x in r)
for g in it.product(range(4),repeat=3):
    assert sum(p[i][B3.index(tuple((g[t]>>B3[i][t])&1 for t in range(3)))] for i in range(8))==1
print('(3) p exactly valid (positivity, 64 deterministic interventions)')
fi=REP[ORB]; v=[int(x) for x in valsI[:,fi]]; X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
gfl=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]; gq=[Fr(x).limit_denominator(10**4) for x in gfl]
assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744))
val=sum(gq[8*i+o]*p[i][o] for i in range(8) for o in range(8))+gq[64]
print('(4) EXACT facet %d (orbit %d) value: %.10e (relative %.10e)  %s'%(fi,ORB,float(val),float(val)/max(v),'VIOLATED' if val<0 else 'not violated'))
# (5) symmetry images
pf=np.array([[float(x) for x in r] for r in p])
cnt={o:set() for o in OPEN}; npf=0
for perm in it.permutations(range(3)):
    for fi_ in range(8):
        for fo in range(8):
            Q=np.zeros((8,8))
            for i in range(8):
                for o in range(8):
                    ib=B3[i]; ob=B3[o]
                    i2=tuple(ib[perm[k]]^B3[fi_][k] for k in range(3)); o2=tuple(ob[perm[k]]^B3[fo][k] for k in range(3))
                    Q[B3.index(i2),B3.index(o2)]=pf[i,o]
            vals=Tn[:,:64]@Q.reshape(-1)+Tn[:,64]
            for f_ in np.where(vals<-1e-9)[0]:
                if canon[f_] in cnt: cnt[canon[f_]].add(int(f_))
            npf+=1
print('(5) %d group images of p; facets of each open orbit violated by some image:'%npf,{o:len(s) for o,s in cnt.items() if s}, ' orbit sizes:',{o:int((canon==o).sum()) for o in OPEN})
print('    facets violated by p itself:',{int(canon[f_]):int(((Tn[:,:64]@pf.reshape(-1)+Tn[:,64])[canon==canon[f_]]<-1e-9).sum()) for f_ in np.where((Tn[:,:64]@pf.reshape(-1)+Tn[:,64])<-1e-9)[0] if canon[f_] in OPEN})
