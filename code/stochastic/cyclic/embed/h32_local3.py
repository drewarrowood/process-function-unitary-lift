"""Round 32 (H.37): factor the coefficients P0, P2 of 36 det L / (4 y0^2 y1^2) (h32_local2.py, orbit 28) as Laurent polynomials in u, and sample them."""
import sympy as sp, numpy as np
a=sp.symbols('a0:3',real=True); u=sp.symbols('u0:3')
P0=-(sp.sin(a[2])*sp.sin(a[1]+a[2])-sp.cos(a[1])+sp.cos(a[2])+sp.cos(a[1]+a[2])-1)
P2=-(-sp.sin(a[0])*sp.sin(a[1])-sp.sin(a[0])*sp.sin(a[2])-sp.sin(a[1])*sp.sin(a[2])+sp.cos(a[0])+sp.cos(a[1])+sp.cos(a[2])-sp.cos(a[0]+a[1]+a[2])-2)
def tou(q): return sp.factor(sp.expand(sp.expand_trig(q).rewrite(sp.exp).subs({sp.exp(sp.I*a[k]):u[k] for k in range(3)}).subs({sp.exp(-sp.I*a[k]):1/u[k] for k in range(3)})))
for q in (P0,P2):
    e=sp.simplify(sp.expand(q.rewrite(sp.exp)))
    e=sp.expand(e).subs({a[k]:-sp.I*sp.log(u[k]) for k in range(3)}); print(sp.factor(sp.simplify(e)))
    f=sp.lambdify(a,q); A=np.random.default_rng(0).uniform(0,2*np.pi,(3,10**6)); v=f(*A); print('min',v.min())
