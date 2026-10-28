"""Round 32 (H.37): exact local expansion of orbit 28 at the corner torus t = 0, in projective coordinates y_k = tan(t_k/2).
M is homogeneous of degree 2 in each x_k = (c_k, s_k), so M(x) >= 0 iff Mh(y) = M(1,y_0;1,y_1;1,y_2) >= 0 (c_k != 0); Mh is a polynomial
matrix in y (degree <= 2 in each y_k) with Laurent entries in u_k = e^{i a_k}:
  Mh[z,w] = sum_{i,o} T[i,o] f_i[z] f_i[w] u^{o.(X_w - X_z)} + c prod_k (1+y_k^2) delta_zw,  e_0 = (1, y), e_1 = (-y, 1).
K = span(e_000, e_001) is the kernel at y = 0 (Mh(0) = diag(rowsum T + c), a-independent).  Schur complement on K:
  S(y) = M_KK - M_KH M_HH^{-1} M_HK,  Mh >= 0 near y = 0  iff  S(y) >= 0.   We expand S exactly (sympy, rational T) to order 4 in y.
usage: orbit"""
import sys, itertools as it, numpy as np, sympy as sp
from fractions import Fraction as F
from h20_common import Tn, canon, B3
from h26_hsos import X
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0])
T=[[sp.Rational(str(F(Tn[f,8*i+o]).limit_denominator(10**4))) for o in range(8)] for i in range(8)]; c=sp.Rational(str(F(Tn[f,64]).limit_denominator(10**4)))
y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3'); ep=sp.Symbol('e')
def e(k,ik,b): return (1 if b==0 else y[k]) if ik==0 else (-y[k] if b==0 else 1)
fi=[[sp.prod([e(k,B3[i][k],B3[z][k]) for k in range(3)]) for z in range(8)] for i in range(8)]
M=sp.zeros(8,8)
for z in range(8):
    for w in range(8):
        s=0
        for i in range(8):
            for o in range(8):
                if T[i][o]!=0: s+=T[i][o]*fi[i][z]*fi[i][w]*sp.prod([u[k]**(B3[o][k]*(X[w][k]-X[z][k])) for k in range(3)])
        if z==w: s+=c*sp.prod([1+y[k]**2 for k in range(3)])
        M[z,w]=sp.expand(s)
M0=M.subs({y[0]:0,y[1]:0,y[2]:0}); print('Mh(0) =',[M0[i,i] for i in range(8)],' offdiag zero:',all(M0[i,j]==0 for i in range(8) for j in range(8) if i!=j))
K=[0,1]; H=[2,3,4,5,6,7]
# scale y -> e*y and expand Schur complement to order e^4 with a Neumann series for M_HH^{-1}
Ms=M.subs({y[k]:ep*y[k] for k in range(3)}); Ms=Ms.applyfunc(sp.expand)
MKK=Ms.extract(K,K); MKH=Ms.extract(K,H); MHK=Ms.extract(H,K); MHH=Ms.extract(H,H)
D0=MHH.subs(ep,0); assert D0.is_diagonal(); D0i=sp.diag(*[1/D0[i,i] for i in range(6)])
E=(MHH-D0).applyfunc(sp.expand)   # O(e)
inv=D0i; term=D0i
for n in range(1,3):   # M_HH^{-1} = D0i - D0i E D0i + D0i E D0i E D0i - ...  (MKH is O(e), so order e^2 suffices for S to e^4)
    term=(-term*E*D0i).applyfunc(lambda q: sp.series(sp.expand(q),ep,0,3).removeO()); inv=inv+term
S=(MKK-MKH*inv*MHK).applyfunc(lambda q: sp.series(sp.expand(q),ep,0,5).removeO())
S=S.applyfunc(sp.expand)
coef={k:S.applyfunc(lambda q: sp.expand(q).coeff(ep,k)) for k in range(5)}
for k in range(5):
    print(f'order e^{k}:',[sp.factor(coef[k][i,j]) for i in range(2) for j in range(2)])
import pickle; pickle.dump(dict(S=S,coef=coef),open(f'/tmp/h32_local_{orb}.pkl','wb'))
