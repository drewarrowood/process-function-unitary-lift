"""Round 31: SOS relaxation of the reduced family in its REAL form.  By the p-independence (h28_others.log, Round 31),
facet value = min over a, t of lambda_min(A(x,u)),  x_k = (c_k, s_k) = (cos t_k/2, sin t_k/2) real,  u_k = e^{i a_k},
    A[z,w] = sum_{i,o} T[i,o] f_i[z] f_i[w] u^{o.(X_w - X_z)} + c prod_k |x_k|^2 delta_zw,   f_i[z] = prod_k e_{i_k}[z_k], e0 = (c,s), e1 = (-s,c).
Relaxation (env D = d0,d1,d2 >= 1, default 1,1,1):  with m = prod_k |x_k|^{2(d_k-1)},
    m (psi^dag A psi - gamma |psi|^2 prod|x_k|^2) = sum_b V_b^dag Q_b V_b  [+ g * sum_b W_b^dag R_b W_b  if REG is set],  Q, R >= 0,
V entries psi_w x^alpha u^m, alpha homogeneous of degree d_k in party k, m in {0..X[w][k]} (U=X, default) or {0,1}^3 (U=full) or {-1,0,1}^3 (U=wide).
Q may be taken REAL symmetric: (psi,u) -> (conj psi, conj u) fixes p and maps Q to Q^T = conj Q, so averaging gives a real Gram.
Blocks split by the parity of (s_k-degree + bit k of w) (the symmetry s_k -> -s_k, psi_w -> (-1)^{w_k} psi_w, i.e. p_k -> p_k + pi).
Coefficient matching is over monomials in the REAL x (so c_k^2 and s_k^2 terms of different Gram entries may combine), Laurent in u.
REG (region term, needs d0,d1 >= 2):  'sw'  g = sin^2 t0 |x1|^4 - sin^2 t1 |x0|^4   (region |sin t0| >= |sin t1|; the swap symmetry of 28/30 covers the rest)
                                       'sw-' g = -that.   'a2' g = 1 - cos a2 (always >= 0; control).
Any feasible gamma is a lower bound for the facet value (on the region, if REG).  usage: orbit [solver]"""
import sys, os, time, itertools as it, numpy as np, scipy.sparse as sp, cvxpy as cp
from h20_common import Tn, canon, B3
from h26_hsos import X
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0]); T=Tn[f,:64].reshape(8,8); c=Tn[f,64]
D=[int(v) for v in os.environ.get('D','1,1,1').split(',')]; U=os.environ.get('U','X'); REG=os.environ.get('REG','')
def padd(P,Q,s=1.0):
    R=dict(P)
    for k,v in Q.items(): R[k]=R.get(k,0)+s*v
    return R
def pmulx(P,Q):   # polys keyed by (xexp6, uexp3)
    R={}
    for (a,m),v in P.items():
        for (b,n),w in Q.items():
            k=(tuple(i+j for i,j in zip(a,b)),tuple(i+j for i,j in zip(m,n))); R[k]=R.get(k,0)+v*w
    return R
def xm(k,b,e=1):
    a=[0]*6; a[2*k+b]=e; return tuple(a)
Z3=(0,0,0); Z6=(0,)*6
def e(k,ik,b):   # e_{ik}[b] for party k as poly
    if ik==0: return {(xm(k,b),Z3):1.0}
    return {(xm(k,1),Z3):-1.0} if b==0 else {(xm(k,0),Z3):1.0}
def nrm(k): return {(xm(k,0,2),Z3):1.0,(xm(k,1,2),Z3):1.0}
# A as dict (z,w) -> poly
fi={}
for i in range(8):
    for z in range(8):
        P={(Z6,Z3):1.0}
        for k in range(3): P=pmulx(P,e(k,B3[i][k],B3[z][k]))
        fi[i,z]=P
N={(Z6,Z3):1.0}
for k in range(3): N=pmulx(N,nrm(k))
mult={(Z6,Z3):1.0}
for k in range(3):
    for _ in range(D[k]-1): mult=pmulx(mult,nrm(k))
gamma=cp.Variable()
target={}   # key (z,w,xexp,uexp) -> const coefficient ; gamma part separately
gpart={}
for z in range(8):
    for w in range(8):
        P={}
        for i in range(8):
            for o in range(8):
                if T[i,o]==0: continue
                uu=tuple(B3[o][k]*(X[w][k]-X[z][k]) for k in range(3))
                P=padd(P,{(a,uu):v*T[i,o] for (a,_),v in pmulx(fi[i,z],fi[i,w]).items()})
        if z==w: P=padd(P,{k:c*v for k,v in N.items()})
        P=pmulx(P,mult)
        for (a,m),v in P.items():
            if abs(v)>1e-15: target[(z,w,a,m)]=target.get((z,w,a,m),0)+v
        if z==w:
            for (a,m),v in pmulx(N,mult).items(): gpart[(z,w,a,m)]=gpart.get((z,w,a,m),0)+v
def homog(k,d): return [xm(k,0,d-j) if j==0 else tuple(x+y for x,y in zip(xm(k,0,d-j),xm(k,1,j))) for j in range(d+1)]
def xbasis(dd):
    out=[]
    for a0 in homog(0,dd[0]):
        for a1 in homog(1,dd[1]):
            for a2 in homog(2,dd[2]): out.append(tuple(x+y+z for x,y,z in zip(a0,a1,a2)))
    return out
def ubasis(w):
    if U=='full': return list(it.product([0,1],repeat=3))
    if U=='wide': return list(it.product([-1,0,1],repeat=3))
    return list(it.product(*[range(X[w][k]+1) for k in range(3)]))
def blocks_for(dd):
    V=[(w,a,m) for w in range(8) for a in xbasis(dd) for m in ubasis(w)]
    par={}
    for v in V: par.setdefault(tuple((v[1][2*k+1]+B3[v[0]][k])%2 for k in range(3)),[]).append(v)
    return list(par.values())
keys={}
def kid(k):
    if k not in keys: keys[k]=len(keys)
    return keys[k]
for k in list(target)+list(gpart): kid(k)
terms=[]   # (Qvar, rows, cols(r*n+s), coefficient)
def add_family(blks,gpoly):
    for bl in blks:
        n=len(bl); Q=cp.Variable((n,n),symmetric=True); R=[];C=[];V_=[]
        for r,(wr,ar,mr) in enumerate(bl):
            for s,(ws,as_,ms) in enumerate(bl):
                ax=tuple(x+y for x,y in zip(ar,as_)); um=tuple(y-x for x,y in zip(mr,ms))
                for (ga,gm),gv in gpoly.items():
                    k=(wr,ws,tuple(x+y for x,y in zip(ax,ga)),tuple(x+y for x,y in zip(um,gm)))
                    R.append(kid(k)); C.append(r*n+s); V_.append(gv)
        terms.append((Q,R,C,V_,n))
add_family(blocks_for(D),{(Z6,Z3):1.0})
if REG:
    if REG in('sw','sw-'):
        s0={(tuple(x+y for x,y in zip(xm(0,0,2),xm(0,1,2))),Z3):4.0}; s1={(tuple(x+y for x,y in zip(xm(1,0,2),xm(1,1,2))),Z3):4.0}
        g=padd(pmulx(s0,pmulx(nrm(1),nrm(1))),pmulx(s1,pmulx(nrm(0),nrm(0))),-1.0)
        if REG=='sw-': g={k:-v for k,v in g.items()}
        dd=[D[0]-2,D[1]-2,D[2]-1]
    elif REG=='a2':
        g={(Z6,Z3):1.0,(Z6,(0,0,1)):-0.5,(Z6,(0,0,-1)):-0.5}; dd=[D[0]-1,D[1]-1,D[2]-1]
    gm={(ga,gm_):v for (ga,gm_),v in g.items()}
    # g's own degree: multiply W basis so that total x degree matches; W basis degree dd (sw), and g homogeneous of degree 4 in parties 0,1
    if REG=='a2': dd=[D[0],D[1],D[2]]
    if REG in ('sw','sw-'): dd=[D[0]-2,D[1]-2,D[2]]
    add_family(blocks_for(dd),gm)
nk=len(keys); cons=[]
expr=0
for Q,R,C,V_,n in terms:
    M=sp.csr_matrix((np.array(V_,dtype=float),(R,C)),shape=(nk,n*n)); expr=expr+M@cp.vec(Q.T)   # vec(Q.T) row-major
tv=np.zeros(nk); gv=np.zeros(nk)
for k,v in target.items(): tv[keys[k]]+=v
for k,v in gpart.items(): gv[keys[k]]+=v
rep=np.zeros(nk,bool); seen=set()
for k,i in keys.items():
    kk=min(k,(k[1],k[0],k[2],tuple(-x for x in k[3])))
    if kk not in seen: seen.add(kk); rep[i]=True
sel=np.where(rep)[0]
cons=[expr[sel]==tv[sel]-gamma*gv[sel]]+[Q>>0 for Q,*_ in terms]
print(f'orbit {orb} D={D} U={U} REG={REG!r}: blocks {len(terms)} sizes {sorted(t[4] for t in terms)[-5:]} sum n^2 {sum(t[4]**2 for t in terms)} keys {nk}',flush=True)
t0=time.time(); prob=cp.Problem(cp.Maximize(gamma),cons)
solver=sys.argv[2] if len(sys.argv)>2 else 'CLARABEL'
try: prob.solve(solver=solver,verbose=False)
except Exception as ex: print('solver error',ex)
print(f'orbit {orb} D={D} U={U} REG={REG!r}: {prob.status} gamma {gamma.value} {time.time()-t0:.1f}s',flush=True)
