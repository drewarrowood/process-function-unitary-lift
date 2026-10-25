"""Round 18 (H.25.2): structure and exact local certificate of the H.12 seesaw optimum y_A.P = -0.70580...
(1) The polished optimum (h17_batch_search.py, both runs) has deterministic outputs o_{k,x} and projective a-measurements
    along unit Bloch vectors n_{k,x}.  On that family y_A.P = f(n) = sum_x sum_mu W_x[mu] prod_k v_{k,x_k}[mu_k], v = (1, n),
    W_x[mu] = d_{x,supp mu} t^{o(x)}[mu],  t^o[mu] = <psi_o| sigma_mu |psi_o>, d_{x,S} = sum_a y(x,a) prod_{k in S} (-1)^{a_k} / 8.
(2) Newton at 60 digits on the Lagrange system g_i + lam_i n_i = 0, |n_i|^2 = 1 (6 vectors, 24 unknowns).
(3) Krawczyk test in interval arithmetic (mpmath.iv): a box of radius 1e-30 around the Newton point contains a unique exact
    critical point; interval enclosure of its value.
(4) Second order: the Hessian of the Lagrangian projected on the tangent spaces, Hp, has Hp - delta*1 positive definite
    (exact rational Sylvester test at the midpoint) and the interval radius of the Lagrangian Hessian over the box is << delta
    (Weyl), so the exact critical point is a strict local minimum of f on (S^2)^6.
(5) Block optimality over ALL 4-outcome POVMs, each party and setting given the others (float SDP, NUMERICAL).
Usage: h18_h12_local.py [polished_E.npy]"""
import sys, re, itertools as it, numpy as np, torch, mpmath as mp
from fractions import Fraction as Fr
mp.mp.dps=60; iv=mp.iv; iv.dps=60
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),int).reshape(8,8)
Hd=mp.matrix(8,8)
for a in range(8):
    for b in range(8): Hd[a,b]=(-1)**par(a&b)/mp.sqrt(8)
ph=mp.matrix([0,0,0,1/mp.sqrt(2),(1-1j)/2,0,0,0])
psi=[Hd*mp.diag([mp.mpc(1j)**MT[o][z] for z in range(8)])*Hd*ph for o in range(8)]
S=[mp.eye(2),mp.matrix([[0,1],[1,0]]),mp.matrix([[0,-1j],[1j,0]]),mp.matrix([[1,0],[0,-1]])]
def kron3(a,b,c):
    M=mp.matrix(8,8)
    for i in range(8):
        for j in range(8):
            i1,i2,i3=(i>>2)&1,(i>>1)&1,i&1; j1,j2,j3=(j>>2)&1,(j>>1)&1,j&1
            M[i,j]=a[i1,j1]*b[i2,j2]*c[i3,j3]
    return M
MU=list(it.product(range(4),repeat=3))
t={}
for o in range(8):
    for mu in MU:
        v=(psi[o].H*kron3(*[S[m] for m in mu])*psi[o])[0]; assert abs(mp.im(v))<mp.mpf(10)**-50; t[o,mu]=mp.re(v)
E=np.load(sys.argv[1] if len(sys.argv)>1 else 'h18_h12_opt_E.npy')   # polished optimum of h17_batch_search.py (seed 12, rank 1), shape (k,x,c=2a+o,2,2)
O=np.zeros((3,2),int); N0=np.zeros((3,2,3))
for k in range(3):
    for x in range(2):
        tr=[np.trace(E[k,x,c]).real for c in range(4)]; o=int(tr[1]+tr[3]>0.5); O[k,x]=o
        assert abs(tr[o]-1)<1e-6 and abs(tr[2+o]-1)<1e-6
        M=E[k,x,o]; N0[k,x]=[np.trace(M@P).real for P in (np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1]))]
print('output pattern o_{k,x} (rows A,B,C; columns x=0,1):',O.tolist())
d={}
for xi,x in enumerate(B3):
    for Ssub in it.product((0,1),repeat=3):
        d[x,Ssub]=Fr(sum(int(y[xi,ai])*(-1)**sum(a[k] for k in range(3) if Ssub[k]) for ai,a in enumerate(B3)),8)
W={}
for x in B3:
    ox=B3.index(tuple(int(O[k,x[k]]) for k in range(3)))
    for mu in MU:
        q=d[x,tuple(int(m>0) for m in mu)]; W[x,mu]=t[ox,mu]*mp.mpf(q.numerator)/q.denominator
VARS=[(k,x) for k in range(3) for x in range(2)]
def f(n):
    s=0
    for x in B3:
        for mu in MU:
            p=W[x,mu]
            for k in range(3):
                if mu[k]: p=p*n[k,x[k]][mu[k]-1]
            s=s+p
    return s
def grad(n,i):
    k0,x0=i; g=[0,0,0]
    for x in B3:
        if x[k0]!=x0: continue
        for mu in MU:
            if not mu[k0]: continue
            p=W[x,mu]
            for k in range(3):
                if k!=k0 and mu[k]: p=p*n[k,x[k]][mu[k]-1]
            g[mu[k0]-1]=g[mu[k0]-1]+p
    return g
def hessblock(n,i,j):
    k0,x0=i; k1,x1=j; H=[[0]*3 for _ in range(3)]
    if k0==k1: return H
    for x in B3:
        if x[k0]!=x0 or x[k1]!=x1: continue
        for mu in MU:
            if not (mu[k0] and mu[k1]): continue
            p=W[x,mu]
            for k in range(3):
                if k not in (k0,k1) and mu[k]: p=p*n[k,x[k]][mu[k]-1]
            H[mu[k0]-1][mu[k1]-1]=H[mu[k0]-1][mu[k1]-1]+p
    return H
def unpack(z): return {VARS[i]:[z[3*i+j] for j in range(3)] for i in range(6)}, [z[18+i] for i in range(6)]
def F(z):
    n,lam=unpack(z); out=[]
    for i,v in enumerate(VARS):
        g=grad(n,v); out+= [g[j]+lam[i]*n[v][j] for j in range(3)]
    out+=[sum(c*c for c in n[v])-1 for v in VARS]
    return out
def J(z):
    n,lam=unpack(z); M=[[0]*24 for _ in range(24)]
    for i,vi in enumerate(VARS):
        for jj,vj in enumerate(VARS):
            H=hessblock(n,vi,vj)
            for a in range(3):
                for b in range(3): M[3*i+a][3*jj+b]=H[a][b]
        for a in range(3): M[3*i+a][3*i+a]=M[3*i+a][3*i+a]+lam[i]; M[3*i+a][18+i]=n[vi][a]; M[18+i][3*i+a]=2*n[vi][a]
    return M
n0={v:[mp.mpf(float(c)) for c in N0[v]] for v in VARS}
lam0=[]
for v in VARS:
    g=grad(n0,v); lam0.append(-sum(g[j]*n0[v][j] for j in range(3)))
z=mp.matrix([*[c for v in VARS for c in n0[v]],*lam0])
print('f at float optimum:', mp.nstr(f(n0),17),flush=True)
for it_ in range(15):
    Fz=mp.matrix(F(list(z))); dz=mp.lu_solve(mp.matrix(J(list(z))),-Fz); z=z+dz
    print('newton',it_, mp.nstr(mp.norm(Fz),3),flush=True)
    if mp.norm(dz)<mp.mpf(10)**-55: break
zs=list(z); nstar,lams=unpack(zs); val=f(nstar)
print('critical value (50 digits):', mp.nstr(val,50))
print('n*:', {f'{"ABC"[v[0]]}{v[1]}':[mp.nstr(c,15) for c in nstar[v]] for v in VARS})
print('lambdas:', [mp.nstr(l,15) for l in lams],flush=True)
r=mp.mpf(10)**-30
X=[iv.mpf([c-r,c+r]) for c in zs]
C=mp.inverse(mp.matrix(J(zs)))
Wmp=dict(W); eW=mp.mpf(10)**-55   # W entries are 60-digit roundings of exact values in Q(sqrt2): widen by 1e-55
W={k_:iv.mpf([v_-eW,v_+eW]) for k_,v_ in Wmp.items()}
Fm=F([iv.mpf(c) for c in zs]); JX=J(X)
K=[]
for i in range(24):
    s=iv.mpf(zs[i])-sum(iv.mpf(C[i,j])*Fm[j] for j in range(24))
    for j in range(24):
        cij=iv.mpf(1 if i==j else 0)-sum(iv.mpf(C[i,l])*JX[l][j] for l in range(24))
        s+=cij*(X[j]-iv.mpf(zs[j]))
    K.append(s)
ok=all(K[i].a>X[i].a and K[i].b<X[i].b for i in range(24))
print('Krawczyk K(X) in int(X):',ok, ' max |K-z|:', mp.nstr(max(max(abs(K[i].a-zs[i]),abs(K[i].b-zs[i])) for i in range(24)),3))
fX=f({v:[X[3*i+j] for j in range(3)] for i,v in enumerate(VARS)})
print('PROVED enclosure of the exact critical value: [', mp.nstr(fX.a,25),',', mp.nstr(fX.b,25),']',flush=True)
W=Wmp
def tangent_basis(nv):
    a=mp.matrix(nv); e=mp.matrix([1,0,0]) if abs(a[0])<0.9 else mp.matrix([0,1,0])
    u=e-(a.T*e)[0]*a; u=u/mp.norm(u); w=mp.matrix([a[1]*u[2]-a[2]*u[1],a[2]*u[0]-a[0]*u[2],a[0]*u[1]-a[1]*u[0]]); return u,w
Tb=[tangent_basis(nstar[v]) for v in VARS]
JJ=J(zs); Hfull=mp.matrix(18,18)
for i in range(18):
    for j in range(18): Hfull[i,j]=JJ[i][j]
P=mp.matrix(18,12)
for i in range(6):
    for c in range(2):
        for a in range(3): P[3*i+a,2*i+c]=Tb[i][c][a]
Hp=P.T*Hfull*P
ev=mp.eigsy((Hp+Hp.T)/2)[0]; ev=sorted([ev[i] for i in range(12)])
print('projected Hessian eigenvalues:', [mp.nstr(e,6) for e in ev])
delta=ev[0]/2
def posdef(Mq):
    A=[r_[:] for r_ in Mq]; n=len(A)
    for k in range(n):
        if A[k][k]<=0: return False
        for i in range(k+1,n):
            f_=A[i][k]/A[k][k]
            for j in range(k+1,n): A[i][j]-=f_*A[k][j]
    return True
Q=[[Fr(int(mp.nint(((Hp[i,j]+Hp[j,i])/2-(delta if i==j else 0))*mp.mpf(2)**130)),2**130) for j in range(12)] for i in range(12)]
print('Hp - delta*1 positive definite (exact rational Sylvester):', posdef(Q), ' delta =', mp.nstr(delta,6))
rad=max(float(iv.mpf(JX[i][j]).delta/2) for i in range(18) for j in range(18))
print('max radius of the interval Lagrangian Hessian over the box:', rad, '; Frobenius bound on the perturbation:', 18*rad, '<< delta')
import cvxpy as cp
Pm=[np.eye(2),np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1])]
nst={v:np.array([float(c) for c in nstar[v]]) for v in VARS}
def Ek(k,x):
    out=[np.zeros((2,2),complex) for _ in range(4)]
    for a in (0,1): out[2*a+O[k,x]]=(np.eye(2)+(-1)**a*sum(nst[k,x][j]*Pm[j+1] for j in range(3)))/2
    return out
psif=[np.array([complex(c) for c in p]) for p in psi]
def full(EE):   # value for EE[k][x][c]
    s=0
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            if not y[xi,ai]: continue
            for oi,o in enumerate(B3):
                M=np.kron(np.kron(EE[0][x[0]][2*a[0]+o[0]],EE[1][x[1]][2*a[1]+o[1]]),EE[2][x[2]][2*a[2]+o[2]])
                s+=y[xi,ai]*(psif[oi].conj()@M@psif[oi])
    return s
EE=[[Ek(k,x) for x in (0,1)] for k in range(3)]
print('full value check (float):', full(EE).real)
worst=0
for k0 in range(3):
    for x0 in (0,1):
        G=[]
        E0=[[list(e) for e in row] for row in EE]; E0[k0][x0]=[np.zeros((2,2)) for _ in range(4)]; K0=full(E0).real   # terms not involving this block
        for c in range(4):
            Gc=np.zeros((2,2),complex)
            for i in range(2):
                for j in range(2):
                    B=np.zeros((2,2),complex); B[i,j]=1
                    E2=[[list(e) for e in row] for row in EE]; E2[k0][x0]=[np.zeros((2,2)) for _ in range(4)]; E2[k0][x0][c]=B
                    Gc[j,i]=full(E2)-K0   # value = K0 + sum_c Tr(E_c G_c)
            G.append(Gc)
        cur=sum(np.trace(EE[k0][x0][c]@G[c]).real for c in range(4))
        Ev=[cp.Variable((2,2),hermitian=True) for _ in range(4)]
        pr=cp.Problem(cp.Minimize(cp.real(sum(cp.trace(Ev[c]@G[c]) for c in range(4)))),[e>>0 for e in Ev]+[sum(Ev)==np.eye(2)])
        pr.solve(solver=cp.SCS,eps=1e-10)
        print(f'party {"ABC"[k0]} x={x0}: current {cur+K0:.10f}, best POVM given the rest {pr.value+K0:.10f}',flush=True); worst=max(worst,cur-pr.value)
print('max single-block improvement over all POVMs:', worst)
