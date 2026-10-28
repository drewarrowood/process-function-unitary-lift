"""Round 33 (H.38): exact transverse coefficient on the two sheets {t0 = 0} and {t0 = pi} of {sin t0 = 0}.
Mh(y) = M0 + y0 M1 + y0^2 M2 (h33_g.py; y_k = tan(t_k/2)).  M0 and M2 are block diagonal in z0 (blocks P = {z0=0}, Q = {z0=1}),
M1 is block off-diagonal (C = M1[P,Q]).
 sheet t0 = 0  : M0 = diag(A0, B0), A0 singular with polynomial kernel vector v, B0 invertible.
                 lambda_min(Mh) = y0^2 * G0 / (det B0 * |v|^2) + O(y0^3),  G0 = det B0 * v^dag A2 v - (C^dag v)^dag adj(B0) (C^dag v).
 sheet t0 = pi : (y0 -> oo, Mh/y0^2 = M2 + M1/y0 + M0/y0^2)  M2 = diag(A2, B2), B2 w = 0, A2 invertible.
                 lambda_min(Mh) = G_pi / (det A2 * |w|^2) + O(1/y0),  G_pi = det A2 * w^dag B0 w - (C w)^dag adj(A2) (C w).
g = lim lambda_min(M)/sin^2 t0 equals c1^2 c2^2 G0/(4 det B0 |v|^2) on t0 = 0 and c1^2 c2^2 G_pi/(4 det A2 |w|^2) on t0 = pi
(where the kernel is one-dimensional).  This script derives G0, G_pi exactly, checks them against direct eigenvalues,
and minimises g numerically on both sheets.  usage: orbit"""
import sys, pickle, time, numpy as np, sympy as sp, torch
from h33_g import build
orb=int(sys.argv[1]); M,y,u,T,c=build(orb)
Mj=[M.applyfunc(lambda q: sp.expand(q).coeff(y[0],j)) for j in range(3)]
P=[0,1,2,3]; Q=[4,5,6,7]
A0,B0,A2,B2=Mj[0].extract(P,P),Mj[0].extract(Q,Q),Mj[2].extract(P,P),Mj[2].extract(Q,Q); C=Mj[1].extract(P,Q)
def conjL(e): return sp.expand(e.subs({u[k]:1/u[k] for k in range(3)},simultaneous=True))
def herm(X): return X.T.applyfunc(conjL)
assert all(Mj[1][i,j]==0 for i in P for j in P) and all(Mj[1][i,j]==0 for i in Q for j in Q)
assert all(Mj[k][i,j]==0 for k in (0,2) for i in P for j in Q)
def kervec(Bk):
    ns=Bk.nullspace(); assert len(ns)==1
    v=ns[0]; den=sp.lcm([sp.fraction(sp.together(x))[1] for x in v]); v=(v*den).applyfunc(lambda q: sp.factor(sp.cancel(q)))
    g=sp.gcd_list([sp.numer(sp.together(x)) for x in v if x!=0]); v=v.applyfunc(lambda q: sp.factor(sp.cancel(q/g)))
    assert (Bk*v).applyfunc(lambda q: sp.simplify(q))==sp.zeros(4,1); return v
print(orb,'det A0, B2 identically 0:',sp.expand(A0.det(method='berkowitz'))==0, sp.expand(B2.det(method='berkowitz'))==0)
dA2=sp.factor(A2.det(method='berkowitz')); print(orb,'det A2 =',dA2)
v=kervec(A0); w=kervec(B2); print(orb,'kernel v (t0=0) =',list(v)); print(orb,'kernel w (t0=pi) =',list(w))
t=time.time()
dB0=sp.expand(B0.det(method='berkowitz')); adjB0=B0.adjugate(method='berkowitz').applyfunc(sp.expand); adjA2=A2.adjugate(method='berkowitz').applyfunc(sp.expand)
Cv=herm(C)*v; Cw=C*w
G0=sp.expand(sp.expand((herm(v)*A2*v)[0])*dB0 - sp.expand((herm(Cv)*adjB0*Cv)[0]))
Gpi=sp.expand(sp.expand((herm(w)*B0*w)[0])*sp.expand(dA2) - sp.expand((herm(Cw)*adjA2*Cw)[0]))
print(orb,f'G0: {len(G0.args)} terms; G_pi: {len(Gpi.args)} terms ({time.time()-t:.1f}s)',flush=True)
pickle.dump(dict(Mj=Mj,A0=A0,B0=B0,A2=A2,B2=B2,C=C,v=v,w=w,G0=G0,Gpi=Gpi,dB0=dB0,dA2=dA2),open(f'h33_exact_o{orb}.pkl','wb'))
fM=sp.lambdify((u,y),M,'numpy'); f0=sp.lambdify((u,y[1],y[2]),[G0,dB0]+list(v),'numpy'); fp=sp.lambdify((u,y[1],y[2]),[Gpi,dA2]+list(w),'numpy')
rng=np.random.default_rng(3); err=0
for _ in range(20):
    a=rng.uniform(0,2*np.pi,3); y1,y2=rng.standard_normal(2); U=np.exp(1j*a)
    r=np.array(f0(U,y1,y2),dtype=complex); g0=(r[0]/r[1]).real/np.vdot(r[2:],r[2:]).real
    l0=np.linalg.eigvalsh(np.array(fM(U,[1e-4,y1,y2]),dtype=complex))[0]/1e-8
    r=np.array(fp(U,y1,y2),dtype=complex); gp=(r[0]/r[1]).real/np.vdot(r[2:],r[2:]).real
    lp=np.linalg.eigvalsh(np.array(fM(U,[1e4,y1,y2]),dtype=complex))[0]
    err=max(err,abs(g0-l0)/(abs(l0)+1e-3),abs(gp-lp)/(abs(lp)+1e-3))
print(orb,f'check vs direct eigenvalues (20 points, y0 = 1e-4 and 1e4): max rel err {err:.1e}')
# numerical minimisation of g on both sheets, homogeneous coords (t1,t2 in [0,pi]); g = c1^2 c2^2 G/(4 det |v|^2)
th=sp.symbols('a0:3 t1 t2',real=True)
def gexpr(G,d,vec):
    s=lambda e: e.subs({u[k]:sp.exp(sp.I*th[k]) for k in range(3)})
    return G,d,vec
F0=sp.lambdify((u,y[1],y[2]),[G0,dB0]+list(v),'numpy'); Fp=sp.lambdify((u,y[1],y[2]),[Gpi,dA2]+list(w),'numpy')
def gnum(F,x):
    a=x[:,:3]; t1=x[:,3]; t2=x[:,4]; U=[np.exp(1j*a[:,k]) for k in range(3)]
    y1=np.tan(t1/2); y2=np.tan(t2/2); r=[np.asarray(q,dtype=complex)*np.ones(len(x)) for q in F(U,y1,y2)]
    nv=sum(np.abs(q)**2 for q in r[2:]); return (np.cos(t1/2)**2*np.cos(t2/2)**2*(r[0]/r[1]).real/nv/4)
from scipy.optimize import minimize
for nm,F in (('t0=0',F0),('t0=pi',Fp)):
    x0=np.c_[rng.uniform(0,2*np.pi,(20000,3)),rng.uniform(0.02,np.pi-0.02,(20000,2))]; gv=gnum(F,x0)
    best=[]; 
    for i in np.argsort(gv)[:60]:
        r=minimize(lambda z: gnum(F,z[None])[0],x0[i],method='Nelder-Mead',options=dict(xatol=1e-10,fatol=1e-14,maxiter=4000)); best.append((r.fun,r.x))
    best.sort(key=lambda q:q[0]); print(orb,nm,f'g on 20000 random points: min {gv.min():.4e} median {np.median(gv):.3e}; after 60 local minimisations: min {best[0][0]:.6e} at a,t1,t2 = {np.round(best[0][1],4)}',flush=True)
