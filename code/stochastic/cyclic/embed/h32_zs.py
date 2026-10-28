"""Round 32 (H.37): zero-set-structured real SOS certificate for the reduced family (built on h31_real.py, same p, same rows).
Identity:  m (psi^dag A psi - gamma |psi|^2 prod|x_k|^2) = sum_b V_b^dag Q_b V_b + sum_j h_j sum_b W_{j,b}^dag R_{j,b} W_{j,b},  Q, R >= 0,
m = prod_k |x_k|^{2(d_k-1)} (env D, plain basis degree DP <= D, default DP = D, lifted by prod |x_k|^{2(D_k-DP_k)}),
h_j = known nonnegative weights vanishing on zero components of orbit 28 (env W = comma list):
  s0 = sin^2 t0 = 4 c0^2 s0^2 (x0-degree 4)    s1 = sin^2 t1    s01 = sin^2 t0 sin^2 t1    s2 = sin^2 t2
  a2 = sin^2(a2/2) = (2 - u2 - 1/u2)/4         a1 = sin^2(a1/2)  a0 = sin^2(a0/2)
  s0a2, s1a2, s01a2 = products;  a12 = sin^2(a1/2)+sin^2(a2/2);  a02 = sin^2(a0/2)+sin^2(a2/2);  a2s2 = sin^2(a2/2)|x2|^4 + sin^2 t2
Region weights (valid only on the region): r0_<delta>, r1_<delta> = sin^2 t_k - delta^2 |x_k|^4  (region |sin t_k| >= delta);
  rc_<delta> = sum_k sin^2 t_k - delta^2 (region away from the corner tori t in {0,pi}^3; needs D >= 2,2,2);
  q<k>_<delta> = sin^2(a_k/2) - delta^2 (region |sin(a_k/2)| >= delta).
Each weighted family uses basis degree D - (x-degree of h_j)/2 and the same u-basis rule (U) as the plain family.
NOTE (cone inclusion): each listed h_j is a sum of Hermitian squares (sin^2 t = (2cs)^2, sin^2(a/2) = |1-u|^2/4), so every h_j W^dag R W
is itself a Gram form in the monomials (2cs) W or (1-u)W/2: the structured cone sits inside the plain cone of the same degree with
the u-support widened by the a-weights.  Any feasible gamma is a lower bound on the facet value.  usage: orbit [out.npz]"""
import sys, os, time, itertools as it, numpy as np, scipy.sparse as sp, cvxpy as cp
from h20_common import Tn, canon, B3
from h26_hsos import X
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0]); T=Tn[f,:64].reshape(8,8); c=Tn[f,64]
D=[int(v) for v in os.environ.get('D','1,1,1').split(',')]; U=os.environ.get('U','X'); REG=os.environ.get('REG','')
DP=[int(v) for v in os.environ.get('DP',','.join(map(str,D))).split(',')]; WL=[w for w in os.environ.get('W','').split(',') if w]
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
BASES=[]
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
        terms.append((Q,R,C,V_,n)); BASES.append(bl)
lift={(Z6,Z3):1.0}
for k in range(3):
    for _ in range(D[k]-DP[k]): lift=pmulx(lift,nrm(k))
add_family(blocks_for(DP),lift)
def sq(k): return {(tuple(x+y for x,y in zip(xm(k,0,2),xm(k,1,2))),Z3):4.0}   # sin^2 t_k = 4 c^2 s^2
def ua(k):
    e=[0,0,0]; e[k]=1; em=[0,0,0]; em[k]=-1; return {(Z6,Z3):0.5,(Z6,tuple(e)):-0.25,(Z6,tuple(em)):-0.25}   # sin^2(a_k/2)
WDEF={'s0':(sq(0),(2,0,0)),'s1':(sq(1),(0,2,0)),'s2':(sq(2),(0,0,2)),'s01':(pmulx(sq(0),sq(1)),(2,2,0)),
      'a0':(ua(0),(0,0,0)),'a1':(ua(1),(0,0,0)),'a2':(ua(2),(0,0,0)),
      's0a2':(pmulx(sq(0),ua(2)),(2,0,0)),'s1a2':(pmulx(sq(1),ua(2)),(0,2,0)),'s01a2':(pmulx(pmulx(sq(0),sq(1)),ua(2)),(2,2,0)),
      'a12':(padd(ua(1),ua(2)),(0,0,0)),'a02':(padd(ua(0),ua(2)),(0,0,0)),
      'a2s2':(padd(pmulx(ua(2),pmulx(nrm(2),nrm(2))),sq(2)),(0,0,2))}
def reg(k,dl):   # region constraint sin^2 t_k - dl^2 |x_k|^4 >= 0  (NOT globally nonnegative: certificate then valid only on the region)
    return padd(sq(k),pmulx(nrm(k),nrm(k)),-dl*dl)
for wn in WL:
    if wn.startswith('r') and not wn.startswith('rc'):   # r0_0.3 / r1_0.3 : region |sin t_k| >= delta
        k=int(wn[1]); dl=float(wn.split('_')[1]); WDEF[wn]=(reg(k,dl),tuple(2 if j==k else 0 for j in range(3)))
    if wn.startswith('rc'):   # rc_0.3 : region sin^2 t0 + sin^2 t1 + sin^2 t2 >= delta^2 (removes the 8 corner tori t in {0,pi}^3)
        dl=float(wn.split('_')[1]); N4=[pmulx(nrm(k),nrm(k)) for k in range(3)]
        g=padd(padd(pmulx(sq(0),pmulx(N4[1],N4[2])),pmulx(sq(1),pmulx(N4[0],N4[2]))),pmulx(sq(2),pmulx(N4[0],N4[1])))
        WDEF[wn]=(padd(g,pmulx(N4[0],pmulx(N4[1],N4[2])),-dl*dl),(2,2,2)); continue
    if wn.startswith('q'):   # q2_0.3 : region |sin(a_k/2)| >= delta
        k=int(wn[1]); dl=float(wn.split('_')[1]); WDEF[wn]=(padd(ua(k),{(Z6,Z3):1.0},-dl*dl),(0,0,0))
for wn in WL:
    h,sh=WDEF[wn]; dd=[D[k]-sh[k] for k in range(3)]; assert min(dd)>=0, ('weight needs higher D',wn)
    add_family(blocks_for(dd),h)
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
nk=len(keys)
tv=np.zeros(nk); gv=np.zeros(nk)
for k,v in target.items(): tv[keys[k]]+=v
for k,v in gpart.items(): gv[keys[k]]+=v
rep=np.zeros(nk,bool); seen=set()
for k,i in keys.items():
    kk=min(k,(k[1],k[0],k[2],tuple(-x for x in k[3])))
    if kk not in seen: seen.add(kk); rep[i]=True
sel=np.where(rep)[0]
print(f'orbit {orb} D={D} DP={DP} W={WL} U={U} REG={REG!r}: blocks {len(terms)} sizes {sorted(t[4] for t in terms)[-5:]} sum n^2 {sum(t[4]**2 for t in terms)} keys {nk} rows {len(sel)}',flush=True)
t0=time.time()
if os.environ.get('CVX'):
    expr=0
    for Q,R,C,V_,n in terms:
        M=sp.csr_matrix((np.array(V_,dtype=float),(R,C)),shape=(nk,n*n)); expr=expr+M@cp.vec(Q.T,order='F')
    cons=[expr[sel]==tv[sel]-gamma*gv[sel]]+[Q>>0 for Q,*_ in terms]
    prob=cp.Problem(cp.Maximize(gamma),cons); prob.solve(solver='CLARABEL')
    print(f'orbit {orb} D={D} U={U} REG={REG!r}: {prob.status} gamma {gamma.value} {time.time()-t0:.1f}s',flush=True); sys.exit()
# direct Clarabel: x = [gamma, svec(Q_1), ...]  (svec: upper triangle column-major, off-diagonal scaled by sqrt 2)
import clarabel
rowmap=-np.ones(nk,int); rowmap[sel]=np.arange(len(sel)); m0=len(sel)
Ri=[];Ci=[];Vv=[]; off=1; PR=[];PC=[];PV=[]; cones=[clarabel.ZeroConeT(m0)]; prow=m0
r2=np.sqrt(2.0)
for Q,R,C,V_,n in terms:
    R=np.array(R); C=np.array(C); V_=np.array(V_,float); r=C//n; s_=C%n
    i=np.minimum(r,s_); j=np.maximum(r,s_); idx=off+j*(j+1)//2+i; sc=np.where(i==j,1.0,1/r2)
    keep=rowmap[R]>=0
    Ri.append(rowmap[R[keep]]); Ci.append(idx[keep]); Vv.append(V_[keep]*sc[keep])
    nt=n*(n+1)//2; PR.append(prow+np.arange(nt)); PC.append(off+np.arange(nt)); PV.append(-np.ones(nt)); cones.append(clarabel.PSDTriangleConeT(n)); prow+=nt; off+=nt
Ri.append(np.arange(m0)); Ci.append(np.zeros(m0,int)); Vv.append(gv[sel])
A=sp.csc_matrix((np.concatenate(Vv+PV),(np.concatenate(Ri+PR),np.concatenate(Ci+PC))),shape=(prow,off))
b=np.r_[tv[sel],np.zeros(prow-m0)]; q=np.zeros(off); q[0]=-1.0
if os.environ.get('SOLVER')=='scs':   # SCS: same cone data (ZeroCone rows first, then PSD triangles; SCS svec = lower triangle column-major = upper row... same order for symmetric)
    import scs
    # SCS 's' cone uses lower-triangular column-major with sqrt2 scaling; reorder our upper-column-major svec rows into it
    rows=[];o=m0
    perm=np.arange(prow)
    for Q,R,C,V_,n in terms:
        nt=n*(n+1)//2; up=[(i,j) for j in range(n) for i in range(j+1)]; pos={ij:t for t,ij in enumerate(up)}
        lo=[(j,i) for i in range(n) for j in range(i,n)]   # column-major lower: (row j >= col i) -> symmetric partner (i,j) upper
        perm[o:o+nt]=o+np.array([pos[(i,j)] for (j,i) in lo]); o+=nt
    A2=A[perm,:]; b2=b[perm]
    data=dict(A=sp.csc_matrix(A2),b=b2,c=q); cone=dict(z=m0,s=[t[4] for t in terms])
    sv=scs.SCS(data,cone,eps_abs=float(os.environ.get('SCS_EPS','1e-7')),eps_rel=float(os.environ.get('SCS_EPS','1e-7')),max_iters=int(os.environ.get('SCS_ITERS','50000')),verbose=False)
    r=sv.solve()
    print(f"orbit {orb} D={D} DP={DP} W={WL} U={U} REG={REG!r}: scs:{r['info']['status']} gamma {r['x'][0]} dual {-r['info']['dobj']} iters {r['info']['iter']} {time.time()-t0:.1f}s",flush=True); sys.exit()
st=clarabel.DefaultSettings(); st.verbose=False; st.max_iter=int(os.environ.get('ITERS','200'))
sol=clarabel.DefaultSolver(sp.csc_matrix((off,off)),q,A,b,cones,st).solve()
print(f'orbit {orb} D={D} DP={DP} W={WL} U={U} REG={REG!r}: {sol.status} gamma {sol.x[0] if sol.x is not None else None} {time.time()-t0:.1f}s',flush=True)
if len(sys.argv)>2: import json as _j; np.savez(sys.argv[2],x=np.array(sol.x),z=np.array(sol.z),sel=sel,m0=m0,sizes=np.array([t[4] for t in terms]),bases=_j.dumps([[ [int(w),list(a),list(m)] for (w,a,m) in bl] for bl in BASES]))
