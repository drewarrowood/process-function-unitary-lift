"""H.15.7d(B''): exact certificate for the H.12 causal-inequality violation.  The optimiser's best instruments (instr2_h12_best.npy)
are rank-1 projective: agent k, setting x measures along a Bloch direction n_{k,x} and emits o_k = x_k.  Round each n_{k,x}
to a RATIONAL point of the unit sphere (inverse stereographic projection of a rational point), so every projector
(1 + n.sigma)/2 has entries in Q(i).  The H.12 board and source have entries in Q(i, sqrt2).  Compute P(a|x) and y.P exactly
(sympy), where y is the integer causal inequality found by instr_search2 (min over all 138,304 deterministic causal
strategies = 0, checked exactly in integers)."""
import sys, numpy as np, itertools as it, sympy as sp
sys.argv=[sys.argv[0]]
import instr_search2 as S, instr_search as IS
B3=IS.B3; th=np.load('instr2_h12_best.npy')
def ratpt(n,den=64):   # rational point on S^2 near n via stereographic projection from (0,0,-1)
    u,v=sp.Rational(round(n[0]/(1+n[2])*den),den),sp.Rational(round(n[1]/(1+n[2])*den),den); d=1+u**2+v**2
    return (2*u/d,2*v/d,(1-u**2-v**2)/d)
X=sp.Matrix([[0,1],[1,0]]);Y=sp.Matrix([[0,-sp.I],[sp.I,0]]);Z=sp.Matrix([[1,0],[0,-1]])
nX=np.array([[0,1],[1,0]]);nY=np.array([[0,-1j],[1j,0]]);nZ=np.diag([1,-1])
Pi={}
for k in range(3):
    for x in (0,1):
        e=S.povm(th[32*(2*k+x):32*(2*k+x+1)])[x]; n=[np.trace(e@P).real for P in (nX,nY,nZ)]
        r=ratpt(n); Pi[k,x,0]=(sp.eye(2)+r[0]*X+r[1]*Y+r[2]*Z)/2; Pi[k,x,1]=sp.eye(2)-Pi[k,x,0]
        assert sum(t**2 for t in r)==1
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
par=lambda x:bin(x).count('1')&1
Hs=sp.Matrix(8,8,lambda a,b:(-1)**par(a&b))/sp.sqrt(8)
ph=sp.Matrix([0,0,0,1/sp.sqrt(2),(1-sp.I)/2,0,0,0])
psis=[sp.expand(Hs*sp.diag(*[sp.I**MT[o][z] for z in range(8)])*Hs*ph) for o in range(8)]
P=sp.zeros(8,8)
for xi,x in enumerate(B3):
    o=B3.index(x); v=psis[o]   # emits o = x
    for ai,a in enumerate(B3):
        M=sp.kronecker_product(Pi[0,x[0],a[0]],Pi[1,x[1],a[1]],Pi[2,x[2],a[2]])
        P[xi,ai]=sp.expand((v.H*M*v)[0])
yv=None
Pf=np.array(P.evalf(30).tolist(),dtype=complex).real
import json
Ypool=[]
m=json.load(open('../switchboard/h13/min_cex.json'))['m']; Hd=IS.Hd
U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
psiA=np.array([1,1,1,0,0,-1,0,0])/2; psiB=np.array([1,1,1,0,0,0,0,0])/np.sqrt(3); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
for p in ([[abs((U13[o]@psiA)[i])**2 for i in range(8)] for o in range(8)],[[abs((U13[o]@psiB)[i])**2 for i in range(8)] for o in range(8)],[[float(B3[i]==lug(*B3[o])) for i in range(8)] for o in range(8)]):
    Ypool+=S.images(S.farkas(np.array(p)))
Ypool=np.unique(np.round(np.array(Ypool),9),axis=0); y=Ypool[np.argmin(Ypool@Pf.ravel())]
yi=[int(round(t)) for t in y]; assert np.allclose(y,yi)
VA=IS.A.toarray().astype(int); print('integer inequality y (row-major x,a):',yi)
print('min over all 138,304 deterministic causal strategies (exact integers):',int((np.array(yi)@VA).min()))
val=sp.radsimp(sp.expand(sum(yi[8*x+a]*P[x,a] for x in range(8) for a in range(8))))
print('rows sum to 1 exactly:',all(sp.simplify(sum(P[x,a] for a in range(8))-1)==0 for x in range(8)))
print('entries >= 0 (numerically, 30 digits):',min(float(sp.re(sp.N(P[x,a],30))) for x in range(8) for a in range(8)), '; max |imag|:', max(abs(float(sp.im(sp.N(P[x,a],30)))) for x in range(8) for a in range(8)))
print('y.P exact =',sp.simplify(val),' = ',sp.N(val,20))
print('rational Bloch directions:',{f'{k}{x}':tuple(sp.Rational(t) for t in ratpt([np.trace(S.povm(th[32*(2*k+x):32*(2*k+x+1)])[x]@Pm).real for Pm in (nX,nY,nZ)])) for k in range(3) for x in (0,1)})
r1=sp.Rational(158077977870324318023361541,108202395271728590997126690); r2=sp.Rational(33154036840568731352429917,21640479054345718199425338)
assert sp.simplify(val-(r1-r2*sp.sqrt(2)))==0
print('sign check in exact rationals: y.P = r1 - r2*sqrt2 with r1,r2 > 0 and r1^2 < 2 r2^2:',r1>0 and r2>0 and r1**2<2*r2**2,'-> EXACT violation')
