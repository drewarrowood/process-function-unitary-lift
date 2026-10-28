"""Round 33 (H.38): SOS relaxation for the core factor H of G0 (sheet t0 = 0), see h33_g2.py.
G0 = (1+y1^2)^a (1+y2^2)^b * Hc / (243 u0^2 u1^2 u2^2); H = Hc/(u0 u1 u2)^2 is a real-valued Laurent polynomial in u (|u_k| = 1), even in y1, y2.
Largest gam with H - gam*(1+y1^2)^d1 (1+y2^2)^d2 = sum_b V_b^dag Q_b V_b, V = y1^i y2^j u^m (i <= d1, j <= d2, m in [-R,R]^3),
Q_b real symmetric PSD (conjugation symmetry), blocks by parity of (i, j).  Native Clarabel (no cvxpy).
usage: orbit [R] [mode: max | face:<zeros.npy>]"""
import sys, pickle, time, itertools as it, numpy as np, sympy as sp, scipy.sparse as sps, clarabel
from math import comb
orb=int(sys.argv[1]); R=int(sys.argv[2]) if len(sys.argv)>2 else 1
a=pickle.load(open(f'h33_exact_o{orb}.pkl','rb')); y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3')
def core_H():
    num,den=sp.fraction(sp.together(a['G0'])); fl=sp.factor_list(num)
    core=[f for f,m in fl[1] if len(sp.expand(f).args)>2]; assert len(core)==1
    P=sp.Poly(sp.expand(core[0]*fl[0]),y[1],y[2],*u)
    return {(m[0],m[1],m[2]-2,m[3]-2,m[4]-2):sp.Rational(c) for m,c in P.terms()}, fl, den
H,fl,den=core_H()
d1=max(k[0] for k in H)//2; d2=max(k[1] for k in H)//2
def canon_k(k): e=k[2:]; ne=tuple(-x for x in e); return k[:2]+max(e,ne)
def key(b1,b2): return (b1[0]+b2[0],b1[1]+b2[1])+tuple(p-q for p,q in zip(b1[2],b2[2]))
us=list(it.product(range(-R,R+1),repeat=3))
basis={}
for i in range(d1+1):
    for j in range(d2+1):
        for m in us: basis.setdefault((i%2,j%2),[]).append((i,j,m))
Nrm={(2*i,2*j,0,0,0):comb(d1,i)*comb(d2,j) for i in range(d1+1) for j in range(d2+1)}
allk=set(canon_k(k) for k in list(H)+list(Nrm))
for b in basis.values():
    for p in range(len(b)):
        for q in range(p,len(b)): allk.add(canon_k(key(b[p],b[q])))
allk=sorted(allk); kid={k:n for n,k in enumerate(allk)}
rhs=np.zeros(len(allk)); nv=np.zeros(len(allk))
for k,c in H.items(): rhs[kid[canon_k(k)]]+=float(c)
for k,c in Nrm.items(): nv[kid[canon_k(k)]]+=c
def build(blocks_basis):
    # variable x = [gam, svec(Q_1), svec(Q_2), ...]; svec: upper triangle column-major, off-diagonal scaled by sqrt2
    I=[];J=[];V=[]; off=1; info=[]
    for b in blocks_basis:
        n=len(b); idx={}
        col=off
        for q in range(n):
            for p in range(q+1):
                kk=kid[canon_k(key(b[p],b[q]))]
                I.append(kk); J.append(col); V.append(1.0 if p==q else 2.0/np.sqrt(2))  # Q_pq + Q_qp = 2 Q_pq = sqrt2 * x
                col+=1
        info.append((off,n)); off=col
    nvar=off
    I+= [kid_ for kid_ in range(len(allk)) if nv[kid_]!=0]; J+=[0]*int((nv!=0).sum()); V+=list(nv[nv!=0])
    Aeq=sps.csc_matrix((V,(I,J)),shape=(len(allk),nvar))
    Apsd=-sps.eye(nvar,format='csc')[1:,:]
    A=sps.vstack([Aeq,Apsd]).tocsc(); b=np.r_[rhs,np.zeros(nvar-1)]
    cones=[clarabel.ZeroConeT(len(allk))]+[clarabel.PSDTriangleConeT(n) for _,n in info]
    return A,b,cones,nvar,info
if __name__=='__main__':
    print(orb,'H: terms',len(H),'half degrees',d1,d2,'blocks',{k:len(v) for k,v in basis.items()},'constraints',len(allk),flush=True)
    A,b,cones,nvar,info=build(list(basis.values()))
    import scs
    c=np.zeros(nvar); c[0]=-1.0
    # SCS svec: lower triangle column-major with sqrt2 off-diagonal scaling; for symmetric Q this equals the upper triangle row-major,
    # i.e. our (p<=q, column-major upper) ordering transposed -> we must reorder.  Build a permutation per block.
    perm=[0]
    for off,n in info:
        ours={}; k=off
        for q in range(n):
            for p in range(q+1): ours[(p,q)]=k; k+=1
        for j in range(n):          # SCS: column j, rows i>=j  -> entry (i,j) == our (j,i) upper
            for i in range(j,n): perm.append(ours[(j,i)])
    perm=np.array(perm); Aeq=A[:len(allk),:][:,perm]
    Apsd=-sps.eye(nvar,format='csc')[1:,:]
    AA=sps.vstack([Aeq,Apsd]).tocsc(); bb=np.r_[rhs,np.zeros(nvar-1)]; cc=c[perm]
    data=dict(A=AA,b=bb,c=cc); cone=dict(z=len(allk),s=[n for _,n in info])
    it_=int(sys.argv[3]) if len(sys.argv)>3 else 50000
    t=time.time(); solver=scs.SCS(data,cone,eps_abs=1e-9,eps_rel=1e-9,max_iters=it_,verbose=False,acceleration_lookback=10)
    sol=solver.solve()
    x=np.empty(nvar); x[perm]=sol['x']
    print(orb,f'R={R}: SCS {sol["info"]["status"]} gamma {x[0]:.6e} dual {-sol["info"]["dobj"]:.6e} iters {sol["info"]["iter"]} ({time.time()-t:.1f}s)',flush=True)
    pickle.dump(dict(x=x,y=sol['y'],info=info,basis=basis,R=R,allk=allk),open(f'/tmp/h33_sos_{orb}_R{R}.pkl','wb'))
