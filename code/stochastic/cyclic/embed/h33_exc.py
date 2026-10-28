"""Round 33 (H.38): the exceptional sets where the kernel of the base block is 2-dimensional.
sheet t0 = pi: ker B2 is 2-dim on {y1 = 0}, {y2 = 0}, {u0 = 1} (B2 charpoly, h33_g2.py); form F = K^dag (B0 - C^dag A2^-1 C) K.
sheet t0 = 0 : ker A0 is 2-dim on {y1 = 0}, {u2 = 1, y2 = 0}, {u0 = u2 = 1}; form F = K^dag (A2 - C B0^-1 C^dag) K.
We compute F exactly (adjugate form: det * F) and print its trace and determinant, factored.  usage: orbit"""
import sys, pickle, sympy as sp
orb=int(sys.argv[1]); a=pickle.load(open(f'h33_exact_o{orb}.pkl','rb'))
y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3')
def conjL(e): return sp.expand(e.subs({u[k]:1/u[k] for k in range(3)},simultaneous=True))
def herm(X): return X.T.applyfunc(conjL)
A0,B0,A2,B2,C=a['A0'],a['B0'],a['A2'],a['B2'],a['C']
def form(sub,base,other,inv_of,Cmat):
    Bs=base.subs(sub); K=Bs.nullspace(); K=[ (k*sp.lcm([sp.fraction(sp.together(x))[1] for x in k])).applyfunc(sp.cancel) for k in K]
    Km=sp.Matrix.hstack(*K); Is=inv_of.subs(sub); d=sp.factor(Is.det()); adj=Is.adjugate().applyfunc(sp.expand); Cs=Cmat.subs(sub)
    F=(herm(Km)*(other.subs(sub)*d - Cs*adj*herm(Cs))*Km).applyfunc(lambda q: sp.factor(sp.expand(q)))
    return Km,d,F
for nm,sub,sheet in [('t0=pi, y1=0',{y[1]:0},'pi'),('t0=pi, y2=0',{y[2]:0},'pi'),('t0=pi, u0=1',{u[0]:1},'pi'),
                     ('t0=0, y1=0',{y[1]:0},'0'),('t0=0, u2=1,y2=0',{u[2]:1,y[2]:0},'0'),('t0=0, u0=u2=1',{u[0]:1,u[2]:1},'0')]:
    if sheet=='pi': Km,d,F=form(sub,B2,B0,A2,herm(C))   # F = K^dag(B0 det A2 - C^dag adj(A2) C)K
    else: Km,d,F=form(sub,A0,A2,B0,C)                   # F = K^dag(A2 det B0 - C adj(B0) C^dag)K
    tr=sp.factor(sp.expand(F.trace())); de=sp.factor(sp.expand(F.det())) if F.shape[0]==2 else None
    print(f'{orb} {nm}: kernel dim {Km.shape[1]}, K = {Km.T.tolist()}; det(inverted block) = {d if len(str(d))<120 else str(d)[:120]+"..."}')
    for i in range(F.shape[0]):
        for j in range(F.shape[1]): s=str(F[i,j]); print(f'    F[{i},{j}] =', s if len(s)<600 else s[:600]+'...')
    print('    det F =', de if len(str(de))<800 else str(de)[:800]+'...',flush=True)
