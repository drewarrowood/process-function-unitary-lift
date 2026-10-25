"""Round 16, item 3 (H.23.3): the intersected lift-A ∩ lift-B dual of h16_liftAB_dual.py, assembled directly as a sparse SCS problem
(the cvxpy compilation of the same model did not finish: ConeMatrixStuffing ran for >20 min at 6.7 GB).  Same mathematics:
for each family L in FAM and each v = (c0,c1,xM,xN,cM,cN):
  S^L_v = [L==A] C_v + sgn_L K^L_v(Lam) - Lam^L_{xM,xN} - (1-T1)G1 - (1-T0)G0 - [xM=0](1-T2)GB +- DB - [xN=0](1-T3)GC +- DC  >= 0,
sgn_A = +1, sgn_B = -1, K^L_v(Lam) = sum_{xL} emb(Lam'_{x,c}, copy xL)/2, Lam'= link multiplier in family-L qubit order.
maximise sum_L sum Tr Lam^L.  Usage: h16_liftAB_scs.py eps [A|AB]   (A alone must reproduce the Round 14 lift-A value -1.27715).
Hermitian blocks are parametrised by n^2 reals; PSD cones are the 32x32 real forms [[Re,-Im],[Im,Re]] in SCS svec order.  [NUMERICAL]"""
import numpy as np, itertools as it, scipy.sparse as sp, scs, sys, os, time, pickle
t0=time.time(); eps=float(sys.argv[1]) if len(sys.argv)>1 else 1e-6; MODE=sys.argv[2] if len(sys.argv)>2 else 'AB'
FAM=[0] if MODE=='A' else [0,1]; LINK=len(FAM)>1
SRC=open('h12_lift_common.py').read(); B3=list(it.product((0,1),repeat=3)); I2=np.eye(2)
def hbasis(n):
    out=[]
    for i in range(n):
        for j in range(i,n):
            if i==j: E=np.zeros((n,n),complex); E[i,i]=1; out.append(E)
            else:
                E=np.zeros((n,n),complex); E[i,j]=E[j,i]=1; out.append(E)
                E=np.zeros((n,n),complex); E[i,j]=1j; E[j,i]=-1j; out.append(E)
    return out
HB16,HB8=hbasis(16),hbasis(8)
LT=[(i,j) for j in range(32) for i in range(j,32)]; SQ=np.array([1. if i==j else 2**.5 for i,j in LT])
def svec(H):
    R=np.block([[H.real,-H.imag],[H.imag,H.real]]); return np.array([R[i,j] for i,j in LT])*SQ
def unsvec(s):
    R=np.zeros((32,32)); 
    for k,(i,j) in enumerate(LT): R[i,j]=R[j,i]=s[k]/SQ[k]
    return R[:16,:16]+1j*R[16:,:16]
Pl=[I2,np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1])]
def op4(q,P):
    M=np.array([[1.]])
    for r in range(4): M=np.kron(M,P if r==q else I2)
    return M
def twirl(S,q): return sum(op4(q,P)@S@op4(q,P).conj().T for P in Pl)/4
def embQ(first):
    Q=np.zeros((16,16))
    for a in range(8):
        for g in (0,1):
            t=B3[a]; dst=(t[0],g,t[1],t[2]) if first==0 else (g,t[0],t[1],t[2]); Q[int(''.join(map(str,dst)),2),a*2+g]=1
    return Q
def mapmat(f,basis): return np.array([svec(f(B)) for B in basis]).T      # 528 x n^2
MAPS={'id':mapmat(lambda X:X,HB16)}
for q in range(4): MAPS[f'tw{q}']=mapmat(lambda X,q=q:X-twirl(X,q),HB16)
QE=[embQ(0),embQ(1)]
def famdata(L):
    os.environ['LIFTP']=str(L); ns={}; exec(SRC,ns)
    perm=[L]+[j for j in range(3) if j!=L]
    orig=lambda t:tuple(t[perm.index(j)] for j in range(3))
    qidx=np.array([B3.index(orig(B3[a])) for a in range(8)])
    return ns,orig,qidx
FD={L:famdata(L) for L in FAM}
for L in FAM:
    qidx=FD[L][2]
    for xl in (0,1): MAPS[f'K{L}{xl}']=mapmat(lambda X,xl=xl,qidx=qidx:QE[xl]@np.kron(X[np.ix_(qidx,qidx)],I2)@QE[xl].T/2,HB8)
MAPS={k:sp.csc_matrix(np.where(abs(M)>1e-14,M,0)) for k,M in MAPS.items()}
# variable layout
off={}; nv=0
def newvar(key,n):
    global nv; off[key]=(nv,n); nv+=n*n
for L in FAM:
    for k in it.product((0,1),(0,1)): newvar(('Lam',L)+k,16)
    for nm in ('G1','G0'):
        for k in it.product(range(4),(0,1),(0,1),range(4),range(4)): newvar((nm,L)+k,16)
    for nm in ('GB','DB','GC','DC'):
        for k in it.product(range(4),range(4),(0,1),range(4)): newvar((nm,L)+k,16)
if LINK:
    for k in it.product(range(8),range(64)): newvar(('link',)+k,8)
print('variables',nv,f'{time.time()-t0:.0f}s',flush=True)
blocks=[]; bvec=[]; ncone=0; CONES=[]
for L in FAM:
    ns,orig,qidx=FD[L]; sg=+1 if L==0 else -1
    for v in it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)):
        c0,c1,xm,xn,cm,cn=v; terms=[(-1,'id',('Lam',L,xm,xn)),(-1,'tw1',('G1',L,c0,xm,xn,cm,cn)),(-1,'tw0',('G0',L,c1,xm,xn,cm,cn))]
        kb=(c0,c1,xn,cn); kc=(c0,c1,xm,cm)
        terms+= [(-1,'tw2',('GB',L)+kb),(+1,'id',('DB',L)+kb)] if xm==0 else [(-1,'id',('DB',L)+kb)]
        terms+= [(-1,'tw3',('GC',L)+kc),(+1,'id',('DC',L)+kc)] if xn==0 else [(-1,'id',('DC',L)+kc)]
        if LINK:
            for xl,cl in ((0,c0),(1,c1)):
                xo=orig((xl,xm,xn)); co=orig((cl,cm,cn))
                terms.append((sg,f'K{L}{xl}',('link',B3.index(xo),16*co[0]+4*co[1]+co[2])))
        cols=[];
        row=[None]*0
        for coef,mp,key in terms:
            o,n=off[key]; M=(-coef)*MAPS[mp]          # A = -(linear part)
            blocks.append((ncone,o,M))
        Cm=ns['Cv'](*v) if L==0 else np.zeros((16,16)); bvec.append(svec(Cm)); CONES.append((L,v)); ncone+=1
print('cones',ncone,f'{time.time()-t0:.0f}s',flush=True)
R,Cc,Vv=[],[],[]
for ci,o,M in blocks:
    Mc=M.tocoo(); R.append(Mc.row+528*ci); Cc.append(Mc.col+o); Vv.append(Mc.data)
A=sp.csc_matrix((np.concatenate(Vv),(np.concatenate(R),np.concatenate(Cc))),shape=(528*ncone,nv))
b=np.concatenate(bvec); c=np.zeros(nv)
diag_idx=[i for i,B in enumerate(HB16) if np.count_nonzero(B)==1 and B[np.nonzero(B)][0]==1]
for L in FAM:
    for k in it.product((0,1),(0,1)):
        o,_=off[('Lam',L)+k]; c[o+np.array(diag_idx)]=-1.0
print('A',A.shape,'nnz',A.nnz,f'{time.time()-t0:.0f}s',flush=True)
solver=scs.SCS(dict(A=A,b=b,c=c),dict(s=[32]*ncone),eps_abs=eps,eps_rel=eps,max_iters=200000,verbose=True)
sol=solver.solve(); x=sol['x']
print('status',sol['info']['status'],'pobj',-sol['info']['pobj'],f'{time.time()-t0:.0f}s',flush=True)
# rigorous-in-floats evaluation of the bound from the returned multipliers (any multipliers give a valid bound)
svals=b-A@x; bound=0.0
for L in FAM:
    trL=-sum(c[off[('Lam',L)+k][0]+np.array(diag_idx)]@x[off[('Lam',L)+k][0]+np.array(diag_idx)] for k in it.product((0,1),(0,1)))
    mins={}
    for ci,(LL,v) in enumerate(CONES):
        if LL!=L: continue
        lam=np.linalg.eigvalsh(unsvec(svals[528*ci:528*(ci+1)]))[0]; k=(v[2],v[3]); mins[k]=min(mins.get(k,9),lam)
    part=trL+16*sum(mins.values()); bound+=part
    print(f'family {"ABC"[L]}: sum Tr Lam {trL:.7f}, min eigs {[f"{m:.2e}" for m in mins.values()]}, contribution {part:.7f}',flush=True)
print(f'LIFT-{MODE} (SCS direct): float bound {bound:.7f}, time {time.time()-t0:.0f}s',flush=True)
pickle.dump(dict(x=x,off=off,FAM=FAM,MODE=MODE),open(f'/tmp/r16/liftscs_{MODE}.pkl','wb'))
