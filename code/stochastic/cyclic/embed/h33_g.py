"""Round 33 (H.38): the transverse coefficient g of orbit 28 (and control 30) on the hypersurface {sin t0 = 0}.
Projective coordinates y_k = tan(t_k/2) (H.37.4): Mh(y) = M0 + y0 M1 + y0^2 M2, with M_j polynomial in (y1, y2) and Laurent in u.
This script builds Mh exactly (same construction as h32_local.py), and inspects the structure of M0 = Mh(y0 = 0).
usage: orbit"""
import sys, itertools as it, numpy as np, sympy as sp
from fractions import Fraction as F
from h20_common import Tn, canon, B3
from h26_hsos import X
def build(orb):
    f=int(np.where(canon==orb)[0][0])
    T=[[sp.Rational(str(F(Tn[f,8*i+o]).limit_denominator(10**4))) for o in range(8)] for i in range(8)]; c=sp.Rational(str(F(Tn[f,64]).limit_denominator(10**4)))
    assert max(abs(float(T[i][o])-Tn[f,8*i+o]) for i in range(8) for o in range(8))<1e-12 and abs(float(c)-Tn[f,64])<1e-12
    y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3')
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
    return M,y,u,T,c
if __name__=='__main__':
    orb=int(sys.argv[1]); M,y,u,T,c=build(orb)
    Mj=[M.applyfunc(lambda q: sp.expand(q).coeff(y[0],j)) for j in range(3)]
    assert (M-Mj[0]-y[0]*Mj[1]-y[0]**2*Mj[2]).applyfunc(sp.expand)==sp.zeros(8,8)
    print('B3',B3); print('X',X)
    for j in range(3):
        nz=[[int(Mj[j][z,w]!=0) for w in range(8)] for z in range(8)]; print(f'M{j} nonzero pattern', nz)
    import pickle; pickle.dump(dict(Mj=Mj),open(f'/tmp/h33_Mj_{orb}.pkl','wb'))
    rng=np.random.default_rng(1); fl=sp.lambdify((u,y[1],y[2]),Mj[0],'numpy')
    for _ in range(5):
        a=rng.uniform(0,2*np.pi,3); yy=rng.standard_normal(2)
        ev=np.linalg.eigvalsh(np.array(fl(np.exp(1j*a),*yy),dtype=complex)); print('eig M0',np.round(ev,6))
