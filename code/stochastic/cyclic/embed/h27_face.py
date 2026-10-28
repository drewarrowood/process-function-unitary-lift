"""Round 27 (H.34.4): facial reduction of the symmetry-reduced Hermitian SOS for one orbit to the zero-set face.
For each weight block b, N_b = orthonormal basis of the orthogonal complement of span{v_b(z)} over exact zeros z (h27_zs.py npz);
Q_b = N_b G_b N_b^dag, G_b >= 0.  Solves (mode gamma) max gamma, or (mode margin) gamma=GAMMA fixed, max t with G_b >= t I, in Rust Clarabel.
usage: problem.json zeros.npz mode [out.npz]
Round 28 options (env): NOQR=1 skips the dense dependent-row check (use only when the rows are known independent, e.g. no zeros);
SOLVER=scs uses SCS (indirect-free, low memory) instead of Clarabel, with SCS_EPS (default 1e-7) and SCS_ITERS (default 200000).
The constraint matrix is assembled sparse, so large bases (MB=full) fit in memory."""
import os
import json, sys, numpy as np, scipy.sparse as sp, clarabel, time
from fractions import Fraction as F
D=json.load(open(sys.argv[1])); Z=np.load(sys.argv[2]); mode=sys.argv[3]; nbk=len(D['blocks'])
Ns=[]
for b in range(nbk):
    W=Z[f'W{b}']; n=W.shape[1]; U,s,Vh=np.linalg.svd(W); s=s/max(s[0],1e-300); r=int((s>1e-10).sum())
    # Q v = 0 for v = W[row]; Q = sum conj(v_r)Q_rs v_s  -> kernel spanned by W rows (as column vectors v);  complement:
    Ns.append(Vh[r:].conj().T if False else None)
    # range of Q must be orthogonal to v: use null space of W (as map C^n -> C^m, columns v^T): N = null(W) means W N = 0
    Ns[-1]=Vh[r:].conj().T          # columns satisfy W @ N = 0
d=[N.shape[1] for N in Ns]; m=[2*x for x in d]; sv=[x*(x+1)//2 for x in m]
print('face dims', sum(d), 'sum d^2', sum(x*x for x in d), flush=True)
rowsR=[[] for _ in range(nbk)]
for ri,row in enumerate(D['rows']):
    w=1.0 if row['part']=='re' else -1j
    for bi,r,s in row['terms']: rowsR[bi].append((ri,r,s,w))
m0=len(D['rows']); cols=[]; off=1; blocks=[]
Acols=[]  # dense per block
for b in range(nbk):
    n=len(D['blocks'][b]['basis']); N=Ns[b]; db=d[b]
    if db==0: blocks.append(None); continue
    R=np.zeros((m0,n*n),complex)
    for ri,r,s,w in rowsR[b]: R[ri,r*n+s]+=w
    # svec(X) of real 2db x 2db -> G -> Q
    L=[]
    for j in range(2*db):
        for i in range(j+1):
            X=np.zeros((2*db,2*db)); X[i,j]=X[j,i]=(1.0 if i==j else 1/np.sqrt(2))
            G=X[:db,:db]+X[db:,db:]+1j*(X[db:,:db]-X[:db,db:]); L.append((N@G@N.conj().T).ravel())
    Bk=np.real(R@np.array(L).T); Bk[np.abs(Bk)<1e-14]=0; blocks.append(sp.csc_matrix(Bk)); del Bk, L, R
nx=1+sum(sv)+(1 if mode=='margin' else 0)
bvec=np.array([float(F(r['rhs'])) for r in D['rows']]); nv=np.array([float(F(r['nv'])) for r in D['rows']])
o=1; offs=[]
for b in range(nbk):
    offs.append(o)
    if blocks[b] is not None: o+=sv[b]
A=sp.hstack([sp.csc_matrix(nv.reshape(-1,1) if mode=='gamma' else np.zeros((m0,1)))]+[blocks[b] for b in range(nbk) if blocks[b] is not None]+([sp.csc_matrix((m0,1))] if mode=='margin' else [])).tocsc()
if mode=='gamma':
    q=np.zeros(nx); q[0]=-1
    cone_rows=[(offs[b],sv[b],m[b]) for b in range(nbk) if d[b]]
    I=[];J=[];V=[]; rr=0
    for o_,s_,m_ in cone_rows:
        for k in range(s_): I.append(rr+k); J.append(o_+k); V.append(-1.0)
        rr+=s_
    G=sp.csc_matrix((V,(I,J)),shape=(rr,nx)); h=np.zeros(rr)
else:
    GAM=float(sys.argv[5]) if len(sys.argv)>5 else 0.0
    bvec=bvec-nv*GAM; q=np.zeros(nx); q[-1]=-1
    I=[];J=[];V=[];h=[]; rr=0
    for b in range(nbk):
        if not d[b]: continue
        k=0
        for j in range(m[b]):
            for i in range(j+1):
                I.append(rr+k); J.append(offs[b]+k); V.append(-1.0)
                if i==j: I.append(rr+k); J.append(nx-1); V.append(1.0)
                k+=1
        rr+=sv[b]
    G=sp.csc_matrix((V,(I,J)),shape=(rr,nx)); h=np.zeros(rr)
Aall=sp.vstack([A,G]).tocsc(); ball=np.r_[bvec,h]
cones=[clarabel.ZeroConeT(m0)]+[clarabel.PSDTriangleConeT(m[b]) for b in range(nbk) if d[b]]
if mode=='margin':
    Aall=sp.vstack([sp.csc_matrix(([1.0],([0],[0])),shape=(1,nx)),Aall]).tocsc(); ball=np.r_[0.0,ball]; cones=[clarabel.ZeroConeT(m0+1)]+cones[1:]
# drop equality rows that are dependent on the face (identities p(z)=0 at zeros) and check consistency
import scipy.linalg as sl
if os.environ.get('NOQR'):
    rk=m0; keep=np.arange(m0); drop=np.array([],int); inc=0
else:
    Ad=A[:,:sum(sv)+1].toarray(); Qr,Rr,piv=sl.qr(Ad.T,pivoting=True,mode='economic'); dg=np.abs(np.diag(Rr)); rk=int((dg>1e-9*dg[0]).sum())
    keep=np.sort(piv[:rk]); drop=np.setdiff1d(np.arange(m0),keep)
    sol_ls=np.linalg.lstsq(Ad[keep].T, Ad[drop].T, rcond=None)[0]   # A[drop] = coef^T A[keep]
    inc=np.abs(bvec[drop]-sol_ls.T@bvec[keep]).max() if len(drop) else 0; del Ad
print('equality rows',m0,'rank',rk,'dropped',len(drop),'max inconsistency of dropped rhs',inc,flush=True)
mk=len(keep); sel=np.r_[keep, m0+np.arange(Aall.shape[0]-m0-(1 if mode=='margin' else 0))]
if mode=='margin':
    Aall=sp.vstack([Aall[[0]],Aall[1:][sel]]).tocsc(); ball=np.r_[ball[0],ball[1:][sel]]; cones=[clarabel.ZeroConeT(mk+1)]+cones[1:]
else:
    Aall=Aall[sel]; ball=ball[sel]; cones=[clarabel.ZeroConeT(mk)]+cones[1:]
if os.environ.get('SOLVER')=='scs':
    import scs
    # SCS psd cone: lower triangle column-wise; Clarabel PSDTriangle: upper triangle column-wise (same sqrt2 scaling). Permute cone rows.
    nz=mk+(1 if mode=='margin' else 0); perm=list(range(nz)); rr=nz
    for b in range(nbk):
        if not d[b]: continue
        mm=m[b]; up={}; k=0
        for j in range(mm):
            for i in range(j+1): up[(i,j)]=k; k+=1
        perm+=[rr+up[(j,i)] for j in range(mm) for i in range(j,mm)]; rr+=k
    perm=np.array(perm); Aall=Aall[perm]; ball=ball[perm]
    t=time.time(); solver=scs.SCS(dict(A=Aall,b=ball,c=q),dict(z=nz,s=[m[b] for b in range(nbk) if d[b]]),eps_abs=float(os.environ.get('SCS_EPS','1e-7')),eps_rel=float(os.environ.get('SCS_EPS','1e-7')),max_iters=int(os.environ.get('SCS_ITERS','200000')),verbose=False)
    r=solver.solve(); x=r['x']; zz=np.empty(len(perm)); zz[perm]=r['y']
    class _S: pass
    sol=_S(); sol.status='scs:'+r['info']['status']; sol.obj_val=r['info']['pobj']; sol.z=zz
    print(D['orbit'], mode, sol.status, 'objective', -sol.obj_val, 'dual', -r['info']['dobj'], f"iters {r['info']['iter']}", f'{time.time()-t:.1f}s', flush=True)
else:
    st=clarabel.DefaultSettings(); st.verbose=False; st.tol_gap_abs=st.tol_gap_rel=st.tol_feas=1e-10; st.max_iter=400
    t=time.time(); s=clarabel.DefaultSolver(sp.csc_matrix((nx,nx)),q,Aall,ball,cones,st); sol=s.solve()
    x=np.array(sol.x); print(D['orbit'], mode, sol.status, 'objective', -sol.obj_val, f'{time.time()-t:.1f}s', flush=True)
if len(sys.argv)>4 and sys.argv[4]!='-':
    np.savez(sys.argv[4], x=x, z=np.array(sol.z), mk=mk, **{f'N{b}':Ns[b] for b in range(nbk)}, d=np.array(d))
