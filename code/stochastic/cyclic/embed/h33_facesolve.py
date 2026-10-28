"""Round 33 (H.38): max-margin SOS on the zero-set face for the t0 = 0 sheet (orbit 28; orbit 30 as control).
Face: Q_b = N_b G_b N_b^T with N_b an exact rational basis of {c : c . V_b(z) = 0 on the zero families of h33_face.py}.
Solve max t s.t. H = sum_b V_b^dag N_b G_b N_b^T V_b, G_b - t I PSD, t <= 1 (Clarabel).  usage: orbit [extra-kernel pkl]"""
import sys, time
orb=sys.argv[1]; extra=sys.argv[2] if len(sys.argv)>2 and sys.argv[2]!="-" else None; ITS=sys.argv[3] if len(sys.argv)>3 else "20000"
sys.argv=['h33_face.py',orb]; _its=ITS
src=open('h33_face.py').read(); exec(src.split("for fam in fams:")[0])
import scipy.linalg as sl, clarabel
from fractions import Fraction
Ks=pickle.load(open(f'/tmp/h33_face_{orb}.pkl','rb'))
def rat_rref(Mz,tol=1e-9):
    """numerical RREF of the row space of Mz, rationalised (denominators <= 1000) and checked."""
    U,sv,Vt=np.linalg.svd(Mz,full_matrices=False); r=(sv>1e-8*sv[0]).sum(); B=Vt[:r]
    _,_,piv=sl.qr(B,pivoting=True); P=np.sort(piv[:r]); R=np.linalg.solve(B[:,P],B)
    Rq=[[Fraction(float(x)).limit_denominator(1000) for x in row] for row in R]
    err=np.abs(np.array([[float(x) for x in row] for row in Rq])-R).max()
    return Rq,P,err
EX=pickle.load(open(extra,'rb')) if extra else {}
Ns={}
for kb,b in basis.items():
    Mz=Ks[kb]
    if kb in EX: Mz=np.vstack([Mz]+[np.vstack([w.real,w.imag]) for w in EX[kb]])
    Rq,P,err=rat_rref(Mz)
    # exact null space of the rational RREF: columns not in P are free
    n=len(b); r=len(P); free=[j for j in range(n) if j not in set(P)]
    N=[[Fraction(0)]*len(free) for _ in range(n)]
    for c,j in enumerate(free):
        N[j][c]=Fraction(1)
        for i,p in enumerate(P): N[p][c]=-Rq[i][j]
    Nf=np.array([[float(x) for x in row] for row in N])
    res=np.abs(Mz@Nf).max()
    print(orb,kb,'kernel rank',r,'face dim',len(free),'RREF rationalisation err',f'{err:.1e}','residual |Mz N|',f'{res:.1e}',
          'max denominator',max(x.denominator for row in Rq for x in row),flush=True)
    Ns[kb]=(N,Nf)
pickle.dump({k:v[0] for k,v in Ns.items()},open(f'/tmp/h33_N_{orb}.pkl','wb'))
# assemble: coefficient of canonical key from G_b
rows=[];cols=[];vals=[]; off=1; info=[]
for kb,b in basis.items():
    Nf=Ns[kb][1]; n,d=Nf.shape
    Kmat=np.array([[kid[canon_k(key(b[p],b[q]))] for q in range(n)] for p in range(n)])
    # coefficient_k = sum_{p,q} [K_pq = k] (N G N^T)_pq = sum_{r<=s} G_rs w_rs ; G symmetric
    col=off
    for s_ in range(d):
        for r_ in range(s_+1):
            W=np.outer(Nf[:,r_],Nf[:,s_]); W=W+W.T if r_!=s_ else W
            acc=np.bincount(Kmat.ravel(),weights=W.ravel(),minlength=len(allk))
            nz=np.nonzero(np.abs(acc)>1e-14)[0]
            sc=1.0 if r_==s_ else 1/np.sqrt(2)      # x = sqrt2 * G_rs for off-diagonal
            rows+=list(nz); cols+=[col]*len(nz); vals+=list(acc[nz]*sc); col+=1
    info.append((off,d)); off=col
nvar=off
Aeq=sps.csc_matrix((vals,(rows,cols)),shape=(len(allk),nvar))
import scs
# SCS: x = [t, svec_SCS(G_b)...]; our svec order (r<=s, column-major upper) equals SCS lower-column-major order after transposition:
# SCS lower col-major enumerates (i>=j) by column j; entry (i,j) == our (j,i). Build permutation.
perm=[0]
for off_,d in info:
    ours={}; k=off_
    for s_ in range(d):
        for r_ in range(s_+1): ours[(r_,s_)]=k; k+=1
    for j in range(d):
        for i_ in range(j,d): perm.append(ours[(j,i_)])
perm=np.array(perm)
Ae=Aeq[:,perm]
# PSD: s = svec(G - tI) = -(-x_G) + ... : rows  -x_G + t*svec(I)   (s = b - A x  => A = [ -svec(I) | I ])
diagI=[]
for off_,d in info:
    for j in range(d):
        for i_ in range(j,d): diagI.append(1.0 if i_==j else 0.0)
diagI=np.array(diagI); m=len(diagI)
Ap=sps.hstack([sps.csc_matrix(-diagI.reshape(-1,1)) * -1 * -1, sps.eye(m,format='csc')*-1]).tocsc()   # s = t*I - (-G)?? fixed below
Ap=sps.hstack([sps.csc_matrix(diagI.reshape(-1,1)), -sps.eye(m,format='csc')]).tocsc()               # s = b - A x = G - t I
At=sps.csc_matrix(([1.0],([0],[0])),shape=(1,nvar))
AA=sps.vstack([Ae,At,Ap]).tocsc(); bb=np.r_[rhs,1.0,np.zeros(m)]
c=np.zeros(nvar); c[0]=-1.0
it_=int(_its)
t0=time.time(); sol=scs.SCS(dict(A=AA,b=bb,c=c),dict(z=len(allk),l=1,s=[d for _,d in info]),eps_abs=1e-9,eps_rel=1e-9,max_iters=it_,verbose=False).solve()
x=np.empty(nvar); x[perm]=sol['x']
print(orb,f'face max-margin (SCS): {sol["info"]["status"]} t = {x[0]:.6e} dual {-sol["info"]["dobj"]:.6e} iters {sol["info"]["iter"]} ({time.time()-t0:.1f}s), face dims',[d for _,d in info],flush=True)
yv=sol['y']; zp=yv[len(allk)+1:]
pickle.dump(dict(x=x,ypsd=zp,info=info,perm=perm,keys=list(basis)),open(f'/tmp/h33_facesol_{orb}.pkl','wb'))
