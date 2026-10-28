"""Round 27 (H.34.5): exact rational certificate on the reduced face.
(1) per weight block b: integer kernel basis K_b (RREF of the numerical kernel rows of the zeros npz, rounded; entries checked
    to be integers within 1e-5), integer complement N_b with K_b N_b = 0 (FLINT rref nullspace);
(2) numerical Q_b from the h27_face.py margin solve, pulled back G0_b = N_b^+ Q_b N_b^+T, rounded to 2^-40;
(3) exact min-norm correction in the affine space {g : A g = b} (A integer, b rational, rows from the exact export), using an
    independent row subset; afterwards ALL rows are re-checked exactly (dropped rows must hold identically);
(4) exact positive-definiteness of every G_b (Hermitian, real form [[Re,-Im],[Im,Re]], fraction-free elimination).
Nothing here is trusted: the output JSON is re-verified by h27_chkA.py and h27_chkB.py.
Round 29: works unchanged on h29_export.py problems.  Env REAL=1: kernel rows are [Re W; Im W] (real kernels, matching
h27_face.py REAL=1).  If the problem lists its monomials (h29), the certificate carries level, mb and each block's monomials.
usage: problem.json zeros.npz face_out.npz cert_out.json"""
import os
import sys, math, json, time, numpy as np, scipy.linalg as sl
from fractions import Fraction as F
from flint import fmpq_mat, fmpz_mat, fmpq, fmpz
D=json.load(open(sys.argv[1])); Z=np.load(sys.argv[2]); FO=np.load(sys.argv[3]); nbk=len(D['blocks']); t0=time.time()
def unsvec(v,m):
    X=np.zeros((m,m)); k=0
    for j in range(m):
        for i in range(j+1):
            X[i,j]=X[j,i]=v[k]*(1 if i==j else 1/np.sqrt(2)); k+=1
    return X
xs=FO['x']; xo=1; Kb=[];Nb=[];G0=[]
for b in range(nbk):
    n=len(D['blocks'][b]['basis']); W=Z[f'W{b}'].conj()
    if os.environ.get('REAL'): W=np.r_[W.real,W.imag]
    s=np.linalg.svd(W,compute_uv=False) if W.size else np.zeros(1); r=int((s>1e-10*max(s[0],1e-300)).sum())
    if r:
        Vh=np.linalg.svd(W)[2][:r]; M=Vh.copy(); piv=[]; rr=0
        for c in range(n):
            if rr==r: break
            p=rr+np.argmax(abs(M[rr:,c]))
            if abs(M[p,c])<1e-9: continue
            M[[rr,p]]=M[[p,rr]]; M[rr]/=M[rr,c]
            for i in range(r):
                if i!=rr: M[i]-=M[i,c]*M[rr]
            rr+=1
        Ki=np.round(M.real).astype(int); assert np.abs(M-Ki).max()<1e-5, (b,np.abs(M-Ki).max())
        K=fmpq_mat(Ki.tolist()); Nn,nd=K.rref()[0].nullspace() if False else (None,None)
        R_,rk=fmpq_mat(Ki.tolist()).rref(); assert rk==r
        # nullspace from RREF: free columns
        Rl=[[F(int(R_[i,j].p),int(R_[i,j].q)) for j in range(n)] for i in range(r)]
        pivs=[next(j for j in range(n) if Rl[i][j]!=0) for i in range(r)]; free=[j for j in range(n) if j not in pivs]
        Ncols=[]
        for fj in free:
            v=[F(0)]*n; v[fj]=F(1)
            for i,pj in enumerate(pivs): v[pj]=-Rl[i][fj]
            L=1
            for x in v: L=math.lcm(L,x.denominator)
            Ncols.append([int(x*L) for x in v])
        N=np.array(Ncols,dtype=np.int64).T if Ncols else np.zeros((n,0),dtype=np.int64)
        Kb.append(Ki)
    else:
        N=np.eye(n,dtype=np.int64); Kb.append(np.zeros((0,n),int))
    assert (np.array(Kb[-1])@N==0).all() if Kb[-1].size and N.size else True
    Nb.append(N); db=FO['d'][b]
    if db:
        m=2*db; sv=m*(m+1)//2; X=unsvec(xs[xo:xo+sv],m); xo+=sv; No=FO[f'N{b}']
        Go=X[:db,:db]+X[db:,db:]+1j*(X[db:,:db]-X[:db,db:]); Q=No@Go@No.conj().T
    else: Q=np.zeros((n,n))
    assert N.shape[1]==db, (b,N.shape,db)
    Pi=np.linalg.pinv(N.astype(float)); G=Pi@Q@Pi.conj().T; G0.append((G+G.conj().T)/2)
d=[N.shape[1] for N in Nb]; print('face dims',sum(d),'sum d^2',sum(x*x for x in d),f'{time.time()-t0:.0f}s',flush=True)
# parameters: per block, Gr_ij (i<=j), Gi_ij (i<j)
poff=[];P=0;pidx=[]
for b in range(nbk):
    db=d[b]; ix={}
    for j in range(db):
        for i in range(j+1): ix[('r',i,j)]=P; P+=1
    for j in range(db):
        for i in range(j): ix[('i',i,j)]=P; P+=1
    pidx.append(ix)
def gr(b,i,j): return pidx[b][('r',min(i,j),max(i,j))]
def gi(b,i,j): return (pidx[b][('i',i,j)],1) if i<j else ((pidx[b][('i',j,i)],-1) if i>j else (None,0))
rowsA=[]; bv=[]
for row in D['rows']:
    acc={}
    for bi,r,s in row['terms']:
        N=Nb[bi]; nzr=np.nonzero(N[r])[0]; nzs=np.nonzero(N[s])[0]
        for i in nzr:
            for j in nzs:
                cf=int(N[r,i])*int(N[s,j])
                if row['part']=='re': k=gr(bi,i,j); acc[k]=acc.get(k,0)+cf
                else:
                    k,sg=gi(bi,i,j)
                    if k is not None: acc[k]=acc.get(k,0)+sg*cf
    rowsA.append({k:v for k,v in acc.items() if v}); bv.append(F(row['rhs']))
m0=len(rowsA); print('params',P,'rows',m0,flush=True)
g0=np.zeros(P)
for b in range(nbk):
    for (t,i,j),k in pidx[b].items(): g0[k]=G0[b][i,j].real if t=='r' else G0[b][i,j].imag
SC=2**40; g0i=[int(round(x*SC)) for x in g0]
Ad=np.zeros((m0,P))
for ri,rw in enumerate(rowsA):
    for k,v in rw.items(): Ad[ri,k]=v
_,Rr,piv=sl.qr(Ad.T,pivoting=True,mode='economic'); dg=np.abs(np.diag(Rr)); rk=int((dg>1e-9*dg[0]).sum()); keep=sorted(piv[:rk])
print('numerical rank',rk,'float residual of rounded g0',np.abs(Ad@(np.array(g0i)/SC)-np.array([float(x) for x in bv])).max(),flush=True)
# exact residual on kept rows (scaled by SC*den): r = b - A g0
res=[bv[ri]-F(sum(v*g0i[k] for k,v in rowsA[ri].items()),SC) for ri in keep]
Ak=fmpz_mat([[rowsA[ri].get(k,0) for k in range(P)] for ri in keep]) if False else None
# Gram AA^T for kept rows (sparse dot products)
kr=[rowsA[ri] for ri in keep]; M=[[0]*rk for _ in range(rk)]
for a in range(rk):
    for c in range(a,rk):
        ra,rc=kr[a],kr[c]
        if len(ra)>len(rc): ra,rc=rc,ra
        s_=sum(v*rc.get(k,0) for k,v in ra.items()); M[a][c]=M[c][a]=s_
print('gram built',f'{time.time()-t0:.0f}s',flush=True)
y=fmpq_mat(M).solve(fmpq_mat([[fmpq(x.numerator,x.denominator)] for x in res]))
print('solved',f'{time.time()-t0:.0f}s',flush=True)
g=[F(x,SC) for x in g0i]
for a in range(rk):
    ya=F(int(y[a,0].p),int(y[a,0].q))
    if ya:
        for k,v in kr[a].items(): g[k]+=v*ya
maxcorr=max(abs(float(g[k]-F(g0i[k],SC))) for k in range(P)); print('max correction',maxcorr,flush=True)
bad=[ri for ri in range(m0) if sum(v*g[k] for k,v in rowsA[ri].items())!=bv[ri]]
print('exact rows violated after correction:',len(bad),flush=True); assert not bad
def posdef(Mx):
    Mx=[row[:] for row in Mx]; m=len(Mx); prev=fmpz(1)
    for k in range(m):
        if Mx[k][k]<=0: return False
        for i in range(k+1,m):
            for j in range(k+1,m): Mx[i][j]=(Mx[i][j]*Mx[k][k]-Mx[i][k]*Mx[k][j])//prev
        prev=Mx[k][k]
    return True
out=[]; allok=True
for b in range(nbk):
    db=d[b]; Gr=[[F(0)]*db for _ in range(db)]; Gi=[[F(0)]*db for _ in range(db)]
    for i in range(db):
        for j in range(db):
            Gr[i][j]=g[gr(b,i,j)]; k,sg=gi(b,i,j); Gi[i][j]=sg*g[k] if k is not None else F(0)
    if db:
        L=1
        for row in Gr+Gi:
            for x in row: L=math.lcm(L,x.denominator)
        Rm=[[fmpz(int((Gr[i][j] if i<db and j<db else Gr[i-db][j-db] if i>=db and j>=db else -Gi[i][j-db] if i<db else Gi[i-db][j])*L)) for j in range(2*db)] for i in range(2*db)]
        ok=posdef(Rm); allok&=ok
        ev=np.linalg.eigvalsh(np.array([[float(x) for x in r_] for r_ in Gr])+1j*np.array([[float(x) for x in r_] for r_ in Gi]))[0]
        if not ok or b%20==0: print(f' block {b} d={db} lambda_min(G) {ev:.2e} exact PD {ok}',flush=True)
    out.append(dict(S=D['blocks'][b]['S'],wt=D['blocks'][b]['wt'],basis=D['blocks'][b]['basis'],N=Nb[b].tolist(),**({'mono':[D['mono'][i] for i in D['blocks'][b]['basis']]} if 'mono' in D else {}),
                    Gr=[[str(x) for x in r_] for r_ in Gr],Gi=[[str(x) for x in r_] for r_ in Gi]))
print('all blocks exactly positive definite:',allok,f'{time.time()-t0:.0f}s')
json.dump(dict(orbit=D['orbit'],facet=D['facet'],gamma='0',**({'level':D['level'],'mb':D['mb']} if 'level' in D else {}),blocks=out),open(sys.argv[4],'w'))
