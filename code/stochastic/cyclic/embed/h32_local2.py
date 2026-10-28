"""Round 32 (H.37): leading form of the corner Schur complement (from h32_local.py).  With S = S2 e^2 + S3 e^3 + S4 e^4 + ...,
S2 = diag(A,0), S3 offdiagonal (b), the rescaling diag(1,1/e) S diag(1,1/e) = e^2 L + O(e^3), L = [[A, b],[conj b, d]], d = S4[1,1].
Prints A, b, d, det L in trig form (u_k = e^{i a_k}) and tests det L >= 0 (exact SOS form if found, and numerically).  usage: orbit"""
import sys, pickle, numpy as np, sympy as sp
orb=int(sys.argv[1]); P=pickle.load(open(f'/tmp/h32_local_{orb}.pkl','rb')); c=P['coef']
y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3'); a=sp.symbols('a0:3',real=True)
A=c[2][0,0]; b=c[3][0,1]; bb=c[3][1,0]; d=c[4][1,1]
assert sp.simplify(c[2][0,1])==0 and sp.simplify(c[2][1,1])==0 and sp.simplify(c[3][0,0])==0 and sp.simplify(c[3][1,1])==0
def trig(q): return sp.simplify(sp.expand_complex(sp.expand(q.subs({u[k]:sp.exp(sp.I*a[k]) for k in range(3)}))).rewrite(sp.cos))
At,dt=trig(A),trig(d); print('6A =',sp.factor(sp.simplify(6*At))); print('6d =',sp.factor(sp.simplify(6*dt)))
print('6b =',sp.factor(6*b)); print('6conj(b) =',sp.factor(6*bb))
detL=sp.expand(A*d-b*bb); dt_=trig(detL); print('36 det L =',sp.factor(sp.simplify(36*dt_)))
f=sp.lambdify((y,a),dt_,'numpy'); rng=np.random.default_rng(0)
Y=rng.standard_normal((3,200000)); Aa=rng.uniform(0,2*np.pi,(3,200000)); v=np.real(f(Y,Aa))/np.sum(Y**2,0)**3
print(f'{orb}: det L / |y|^6 over 2e5 random points: min {v.min():.3e} median {np.median(v):.3e}')
pickle.dump(dict(A=A,b=b,bb=bb,d=d,detL=detL),open(f'/tmp/h32_lead_{orb}.pkl','wb'))
