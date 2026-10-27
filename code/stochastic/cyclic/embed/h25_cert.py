"""Round 25 (H.32.2): exact dual certificates for R (H.31.2-3) on a kernel forced by the zero set (h25_zeroset.py), not read off an SCS dual.
Same certificate format and checker A as h24_cert.py (checker B = h24_certB.py works on the json unchanged).  Steps: exact rational basis of
span{w_i over the zero set} = K_i;  H_i = P_i G_i P_i^T with P_i an exact basis of K_i^perp;  max-margin  max t: equations, G_i >= t I  (SCS or
CLARABEL);  if t > 0: round, exact correction on pivot columns (flint), exact PD check.
usage: orbit zeroset.npz [tag] [SCS|CLARABEL] [facet]   (writes h25_cert_o<orbit><tag>.json)"""
import sys, json, itertools as it, numpy as np, time
from fractions import Fraction as Fr
import flint
sys.set_int_max_str_digits(0)
fq=lambda x: flint.fmpq(int(Fr(x).numerator),int(Fr(x).denominator))
from h24_sdp2 import classes, Model
from h23_span import ipat
from h20_common import canon, Tn, valsI, PF
import h24_conic as C
orb=int(sys.argv[1]); ZSFILE=sys.argv[2]; TAG=sys.argv[3] if len(sys.argv)>3 else ''; SOLVER=sys.argv[4] if len(sys.argv)>4 else 'SCS'; SOPTS=dict(eps=1e-7,max_iters=200000,verbose=False) if SOLVER=='SCS' else {}; f=int(sys.argv[5]) if len(sys.argv)>5 else int(np.where(canon==orb)[0][0]); assert canon[f]==orb; assert canon[f]==orb; t0=time.time()
X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
v=[int(x) for x in valsI[:,f]]; g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]
gq=[Fr(x).limit_denominator(10**4) for x in g]
assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744))
key,inv,idx,conj=classes(4); n=len(key)
cnt=np.zeros((8,n),int)
for o,z,zp in it.product(range(8),repeat=3): cnt[o,idx[8*o+z,8*o+zp]]+=1
Wq=[[sum(gq[8*i+o]*int(cnt[o,c]) for o in range(8)) for c in range(n)] for i in range(8)]
g0=gq[64]; scale=float(valsI[:,f].max())
# exact kernels from the zero set (h25_zeroset.py): complementary slackness forces span{w_i} into ker H_i (H.32.1)
def ratc(x,D=64): return (Fr(float(x.real)).limit_denominator(D),Fr(float(x.imag)).limit_denominator(D))
import os
RATD=int(os.environ.get('RATD','64'))   # max denominator when rationalising kernel bases
MARGIN=float(os.environ.get('MARGIN','1e-5'))   # a margin below this is treated as 0 (solver tolerance ~1e-7)
KEXTRA=np.load(os.environ['KEXTRA']) if os.environ.get('KEXTRA') else None
ZS=np.load(ZSFILE); Ps=[]; Kdims=[]
for i in range(8):
    W=ZS[f'W{i}']
    _,sv,Vh=np.linalg.svd(W); r_=int((sv/sv[0]>1e-4).sum()); assert r_==len(sv) or sv[r_-1]/sv[r_]>1e3, 'no clear gap in the zero-set span'; Kt=Vh[:r_]   # unit rows spanning the zero-set vectors
    if KEXTRA is not None and f'K{i}' in KEXTRA and len(KEXTRA[f'K{i}']):
        Kx=KEXTRA[f'K{i}']; Kt=np.r_[Kt,Kx/np.linalg.norm(Kx,axis=1)[:,None]]       # facial-reduction vectors, unit norm
        svx=np.linalg.svd(Kt,compute_uv=False); assert svx[-1]>1e-3, f'facial-reduction vectors dependent on the kernel (sv {svx[-1]:.1e})'
        r_=Kt.shape[0]; W=np.r_[W,Kx]
    from scipy.linalg import qr
    _,_,piv=qr(Kt,pivoting=True); R=np.linalg.solve(Kt[:,piv[:r_]],Kt)
    Rq=[[ratc(x,RATD) for x in row] for row in R]
    assert np.abs(np.array([[complex(float(a),float(b)) for a,b in row] for row in Rq])-R).max()<1e-5, 'zero-set span not rational'
    assert all(b==0 for row in Rq for a,b in row), 'complex kernel (not handled)'
    K=flint.fmpq_mat([[fq(a) for a,b in row] for row in Rq])
    # every zero vector must lie in the exact span (re-check numerically against the rational basis)
    Kf=np.array([[float(a) for a,b in row] for row in Rq]); res=W-(W@np.linalg.pinv(Kf))@Kf; rmax=np.abs(res).max()/np.abs(W).max(); assert rmax<1e-4, f'rational span misses zero vectors ({rmax:.1e})'
    Rk,rkK=K.rref(); Rk=[[Fr(int(Rk[a,b].p),int(Rk[a,b].q)) for b in range(64)] for a in range(rkK)]
    pv=[next(b for b in range(64) if Rk[a][b]!=0) for a in range(rkK)]; free=[b for b in range(64) if b not in pv]
    cols=[]
    for fr_ in free:
        vec=[Fr(0)]*64; vec[fr_]=Fr(1)
        for a,pb in enumerate(pv): vec[pb]=-Rk[a][fr_]
        cols.append(vec)
    P=[[cols[j][a] for j in range(len(free))] for a in range(64)]
    Ps.append(P); Kdims.append(rkK); print('H',i,'kernel (zero-set span) dim',rkK,f'(max rel. residual of zero vectors {rmax:.1e})','-> G size',len(free),flush=True)
# unknowns: per i, G_i = A + iB (A sym, B antisym), r x r ; variable list
var=[]
for i in range(8):
    r=len(Ps[i][0])
    for s in range(r):
        for t in range(s,r): var.append((i,'A',s,t))
    for s in range(r):
        for t in range(s+1,r): var.append((i,'B',s,t))
vid={v_:k for k,v_ in enumerate(var)}
# h_c(i) = sum_{(a,b) in c} sum_{s,t} P[a,s] G[s,t] P[b,t]  (P real).  Coefficients CC[c] = P^T E_c P  (r x r)
Pn=[np.array([[float(x) for x in row] for row in P]) for P in Ps]
den=1
for P in Ps:
    for row in P:
        for x in row: den=int(np.lcm(den,x.denominator))
Pi=[np.array([[int(x*den) for x in row] for row in P],dtype=object) for P in Ps]   # integer, P = Pi/den
mem=[[] for _ in range(n)]
for a in range(64):
    for b in range(64): mem[idx[a,b]].append((a,b))
reps=[c for c in range(n) if conj[c]>=c]
rows=[]; rhs=[]   # equations over Q: sum coef*var = rhs  (coef scaled by den^2 -> integers)
DELTA=Fr(os.environ.get('DELTA','0'))   # diagnostic only: certify facet >= -DELTA (relative units x scale); 0 for proofs
mu=-g0-DELTA*Fr(scale).limit_denominator(1)  # bound mu+g0 = -DELTA*scale
for c in reps:
    z,zp,e=inv[c]; Gp=ipat(z,zp); isr=(z==zp and e==(0,0,0))
    # CCi[i] (integer, = den^2 * P^T E_c P)
    CC=[]
    for i in range(8):
        r=Pi[i].shape[1]; Mx=np.zeros((r,r),dtype=object)
        for (a,b) in mem[c]: Mx+=np.outer(Pi[i][a],Pi[i][b])
        CC.append(Mx)
    for gr in Gp:
        # real part: sum_i gr[i] (W[i,c] - mu*isr - Re h_c(i)) = 0 ; Re h = sum A_st CC_st (sym part) - B_st (CC_st - CC_ts)... 
        # G[s,t] = A[s,t] + i B[s,t], A sym, B antisym:  h = sum_{s,t} G[s,t] CC[s,t]
        # Re h = sum_{s<=t} A_st (CC_st + CC_ts [s<t]) ;  Im h = sum_{s<t} B_st (CC_st - CC_ts)
        dre={}; dim={}
        for i in range(8):
            if gr[i]==0: continue
            r=CC[i].shape[0]
            for s in range(r):
                for t in range(s,r):
                    cf=CC[i][s,t]+(CC[i][t,s] if s<t else 0)
                    if cf: dre[vid[(i,'A',s,t)]]=dre.get(vid[(i,'A',s,t)],0)+int(gr[i])*cf
                    if s<t:
                        cf=CC[i][s,t]-CC[i][t,s]
                        if cf: dim[vid[(i,'B',s,t)]]=dim.get(vid[(i,'B',s,t)],0)+int(gr[i])*cf
        rre=sum(int(gr[i])*(Wq[i][c]-(mu if isr else 0)) for i in range(8))*den*den
        rows.append(dre); rhs.append(Fr(rre))
        if conj[c]!=c: rows.append(dim); rhs.append(Fr(0))
print('equations',len(rows),'unknowns',len(var),f'{time.time()-t0:.0f}s',flush=True)
L=np.zeros((len(rows),len(var)))
for k,d_ in enumerate(rows):
    for j,cf in d_.items(): L[k,j]=float(cf)
x0=np.zeros(len(var))
bn=np.array([float(b) for b in rhs])
# max-margin interior point on the reduced face (Clarabel): max t s.t. L x = b, E_i(x) - t I PSD (real embedding of G_i)
import cvxpy as cp, scipy.sparse as sps
psdc=[]; xv=cp.Variable(len(var)); tv=cp.Variable(); rn=np.maximum(np.abs(L).max(1),1e-300); Ln=L/rn[:,None]; bnn=bn/rn   # row scaling for the numerics only
cons=[sps.csr_matrix(Ln)@xv==bnn, cp.abs(xv)<=1e3]
for i in range(8):
    r=Pi[i].shape[1]; Ri=[];Ci=[];Vi=[]
    for (ii,kind,s_,t_),j in vid.items():
        if ii!=i: continue
        if kind=='A':
            for (a,b) in {(s_,t_),(t_,s_),(r+s_,r+t_),(r+t_,r+s_)}: Ri.append(a*2*r+b); Ci.append(j); Vi.append(1.0)
        else:   # E = [[A,-B],[B,A]], B[s,t]=x, B[t,s]=-x
            for (a,b,sg) in [(s_,r+t_,-1),(t_,r+s_,1),(r+s_,t_,1),(r+t_,s_,-1)]: Ri.append(a*2*r+b); Ci.append(j); Vi.append(sg)
    Mi=sps.csr_matrix((Vi,(Ri,Ci)),shape=(4*r*r,len(var))); E=cp.reshape(Mi@xv,(2*r,2*r),order='C')
    cons.append((E+E.T)/2-tv*np.eye(2*r)>>0); psdc.append((i,r,cons[-1]))
try:
    pr=cp.Problem(cp.Maximize(tv),cons); pr.solve(solver=SOLVER,**SOPTS)
    print('max-margin solve',pr.status,'margin t',tv.value,f'{time.time()-t0:.0f}s',flush=True)
    if pr.status in ('optimal','optimal_inaccurate') and tv.value>MARGIN:
        x0=xv.value; print('numeric residual (max-margin point, row-scaled)',np.abs(Ln@x0-bnn).max(),flush=True)
    else:
        # facial reduction step: the PSD multipliers Y_i (sum tr Y_i = 1) of the max-margin problem satisfy the homogeneous adjoint equations;
        # any certificate on this face has <G_i, Y_i> = 0, so range(P_i Y_i P_i^T) must join ker H_i.  Save P_i * range(Y_i) as new kernel vectors.
        out={}
        for (i,r,cn) in psdc:
            Yr=cn.dual_value; Yr=(Yr+Yr.T)/2; Y=(Yr[:r,:r]+Yr[r:,r:])+1j*(Yr[r:,:r]-Yr[:r,r:])   # complex form of the real-embedded multiplier
            ev,U=np.linalg.eigh(Y); ev=ev[::-1]; U=U[:,::-1]; tr=ev.sum()
            k_=int((ev>1e-4*max(ev[0],1e-300)).sum())
            print(f'  Y_{i}: trace {tr:.3e}, top eigs {np.array2string(ev[:6],precision=2)}, numerical rank {k_}',flush=True)
            new=(Pn[i]@U[:,:k_]).T if ev[0]>1e-6*abs(tr)+1e-12 else np.zeros((0,64))
            old=KEXTRA[f'K{i}'] if (KEXTRA is not None and f'K{i}' in KEXTRA) else np.zeros((0,64))
            out[f'K{i}']=np.r_[old,new]      # cumulative over facial-reduction steps
        np.savez_compressed(f'/tmp/r25/h25_fr_o{orb}{TAG}.npz',**out)
        sys.exit(f'margin {tv.value:.2e} <= 0 on this face: facial-reduction vectors saved to /tmp/r25/h25_fr_o{orb}{TAG}.npz')
except Exception as ex: sys.exit(f'max-margin solve failed ({type(ex).__name__}: {ex})')
# rows/cols to pivot on
from scipy.linalg import qr
_,Rr,pr=qr(Ln.T,pivoting=True,mode='economic'); rk=int((np.abs(np.diag(Rr))>1e-8*abs(Rr[0,0])).sum()); R_=sorted(pr[:rk])
_,Rc,pc=qr(Ln[R_],pivoting=True,mode='economic'); Cp=sorted(pc[:rk]); print('rank',rk,flush=True)
xq=[Fr(int(round(float(x)*2**24)),2**24) for x in x0]   # coarse dyadic rounding: the margin t >> rounding error
Cs=set(Cp); res=[rhs[k]-sum(cf*xq[j] for j,cf in rows[k].items() if j not in Cs) for k in R_]
Am=flint.fmpq_mat([[fq(rows[k].get(j,0)) for j in Cp] for k in R_]); bm=flint.fmpq_mat([[fq(r_)] for r_ in res])
sx=Am.solve(bm); 
for a,j in enumerate(Cp): xq[j]=Fr(int(sx[a,0].p),int(sx[a,0].q))
print('exact solve done; max correction',max(abs(float(xq[j])-x0[j]) for j in Cp),f'{time.time()-t0:.0f}s',flush=True)
assert all(sum(cf*xq[j] for j,cf in rows[k].items())==rhs[k] for k in range(len(rows))), 'dependent rows inconsistent'
# exact PD check of each G_i via real embedding [[A,-B],[B,A]]: positive leading principal minors by fraction-free elimination
Gs=[]
for i in range(8):
    r=Pi[i].shape[1]; A=[[Fr(0)]*r for _ in range(r)]; B=[[Fr(0)]*r for _ in range(r)]
    for s in range(r):
        for t in range(s,r):
            A[s][t]=A[t][s]=xq[vid[(i,'A',s,t)]]
            if s<t: B[s][t]=xq[vid[(i,'B',s,t)]]; B[t][s]=-B[s][t]
    Gs.append((A,B))
json.dump(dict(orbit=orb,facet=f,g=[str(x) for x in gq],mu=str(mu),
               P=[[[str(x) for x in row] for row in P] for P in Ps],
               GA=[[[str(x) for x in row] for row in A] for A,B in Gs],GB=[[[str(x) for x in row] for row in B] for A,B in Gs]),
          open(f'h25_cert_o{orb}{TAG}.json','w'))
def posdef(Mq):
    """exact: all pivots of symmetric Gaussian elimination positive (flint fmpq)"""
    m=len(Mq); a=[[flint.fmpq(x.numerator,x.denominator) for x in row] for row in Mq]
    for k in range(m):
        if a[k][k]<=0: return False
        ak=a[k]; inv=1/ak[k]
        for r_ in range(k+1,m):
            fct=a[r_][k]*inv
            if fct!=0:
                ar=a[r_]
                for c_ in range(k,m): ar[c_]-=fct*ak[c_]
    return True
ok=True
for i,(A,B) in enumerate(Gs):
    r=len(A); E=[[A[s][t] for t in range(r)]+[-B[s][t] for t in range(r)] for s in range(r)]+[[B[s][t] for t in range(r)]+[A[s][t] for t in range(r)] for s in range(r)]
    pd=posdef(E); ok&=pd; print('  G',i,'exactly positive definite:',pd,flush=True)
print(f'CHECKER A orbit {orb} facet {f}: certificate {"VALID" if ok else "INVALID"}; bound mu+g0 = {mu+g0}  {time.time()-t0:.0f}s')
