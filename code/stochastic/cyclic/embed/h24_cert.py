"""Round 24 (H.31.1): exact dual certificates for the reduced class-lift relaxation R(w') of PF phase boards on Lugano rule 4.
Relaxation R (no X cone): complex numbers Z_c(i) (i = 0..7, c a class (z,z',e) of h24_sdp2.classes), with Z_{c*}(i) = conj Z_c(i);
  (1) the 64 x 64 Hermitian Z(i)[(o,z),(o',z')] = Z_{class}(i) is PSD;  (2) i -> Z_c(i) lies in span_C ipat(z,z');  (3) sum_z sum_i Z_{(z,z,0)}(i) = 1.
Every PF phase board on rule 4 gives a point of R (Z(i) = diag(1(x)conj f_i) X diag(1(x)f_i), X = v v^dag lifted; mixed sources by convexity)
with facet value  sum_{i,c} W[i,c] Z_c(i) + g0,   W = g (8x8, [i,o]) @ cnt,  cnt[o,c] = #{(z,z'): ((o,z),(o,z')) in c}.
Certificate: Hermitian H_i >= 0 and mu with, for every class c:  ipat(z,z') . (W[:,c] - conj h_c - mu [c=(z,z,0)]) = 0,  h_c(i) = sum_{(a,b) in c} H_i[a,b].
Then value - g0 = sum_i <H_i, Z(i)> + mu >= mu, so mu + g0 >= 0 proves the facet on R.
Construction: SCS dual -> exact rational kernels (facial reduction) -> H_i = P_i G_i P_i^dag -> rounded G -> exact correction (flint) -> exact PD check.
usage: orbit [eps] [tag]   (writes h24_cert_o<orbit><tag>.json; checker A runs at the end)"""
import sys, json, itertools as it, numpy as np, time
from fractions import Fraction as Fr
import flint
fq=lambda x: flint.fmpq(int(Fr(x).numerator),int(Fr(x).denominator))
from h24_sdp2 import classes, Model
from h23_span import ipat
from h20_common import canon, Tn, valsI, PF
import h24_conic as C
orb=int(sys.argv[1]); EPS=float(sys.argv[2]) if len(sys.argv)>2 else 1e-9; TAG=sys.argv[3] if len(sys.argv)>3 else ''; f=int(np.where(canon==orb)[0][0]); t0=time.time()
X=np.c_[PF.reshape(744,-1),np.ones(744,int)]
v=[int(x) for x in valsI[:,f]]; g=np.linalg.lstsq(X.astype(float),np.array(v,float),rcond=None)[0]
gq=[Fr(x).limit_denominator(10**4) for x in g]
assert all(sum(gq[j]*int(X[r,j]) for j in range(65) if X[r,j])==v[r] for r in range(744))
key,inv,idx,conj=classes(4); n=len(key)
cnt=np.zeros((8,n),int)
for o,z,zp in it.product(range(8),repeat=3): cnt[o,idx[8*o+z,8*o+zp]]+=1
Wq=[[sum(gq[8*i+o]*int(cnt[o,c]) for o in range(8)) for c in range(n)] for i in range(8)]
g0=gq[64]; scale=float(valsI[:,f].max())
# numeric dual of R (SCS)
M=Model(4); T=Tn[f,:64].reshape(8,8); W=T@M.cnt; q=np.zeros(M.nv)
for i in range(8):
    for c in range(M.n): q[M.va[1+i][M.rep(c)]]+=W[i,c]
sol=C.solve_scs(q,M.Aeq,M.beq,M.blocks[1:],M.nv,eps=EPS,max_iters=400000)
print('SCS',sol['info']['status'],'bound (relative)',sol['info']['dobj']+Tn[f,64],f'{time.time()-t0:.0f}s',flush=True)
y=sol['y']; off=M.Aeq.shape[0]; il=[(a,b) for b in range(128) for a in range(b,128)]
Hs=[]
for m in range(8):
    vv=y[off:off+len(il)]; off+=len(il); S=np.zeros((128,128))
    for k,(a,b) in enumerate(il): S[a,b]=S[b,a]=vv[k]/(1 if a==b else np.sqrt(2))
    Hs.append((S[:64,:64]+S[64:,64:]+1j*(S[64:,:64]-S[:64,64:]))*scale)   # <S,emb(Z)> = Re tr(H Z) with this H
# exact kernels: rref of numerical kernel basis, rounded to small denominators
def ratc(x,D=64): return (Fr(float(x.real)).limit_denominator(D),Fr(float(x.imag)).limit_denominator(D))
Ps=[]
for i,H in enumerate(Hs):
    ev,U=np.linalg.eigh(H); ev=ev[::-1]; U=U[:,::-1]; rat=ev[:-1]/np.maximum(np.abs(ev[1:]),1e-300); rr=int(np.argmax(rat[:48]))+1
    assert rat[rr-1]>1e4, 'no clear rank gap'
    Kn=U[:,rr:]; Kt=Kn.conj().T
    from scipy.linalg import qr
    _,_,piv=qr(Kt,pivoting=True); R=np.linalg.solve(Kt[:,piv[:Kt.shape[0]]],Kt)
    Rq=[[ratc(x,8) for x in row] for row in R]
    assert np.abs(np.array([[complex(float(a),float(b)) for a,b in row] for row in Rq])-R).max()<1e-4, 'kernel not rational'
    assert all(b==0 for row in Rq for a,b in row), 'complex kernel (not handled)'
    K=flint.fmpq_mat([[fq(a) for a,b in row] for row in Rq])            # rows span kernel (real)
    # P: exact basis of the orthogonal complement = nullspace of K
    Rk,rkK=K.rref(); Rk=[[Fr(int(Rk[a,b].p),int(Rk[a,b].q)) for b in range(64)] for a in range(rkK)]
    pv=[next(b for b in range(64) if Rk[a][b]!=0) for a in range(rkK)]; free=[b for b in range(64) if b not in pv]
    cols=[]
    for fr_ in free:
        vec=[Fr(0)]*64; vec[fr_]=Fr(1)
        for a,pb in enumerate(pv): vec[pb]=-Rk[a][fr_]
        cols.append(vec)
    P=[[cols[j][a] for j in range(len(free))] for a in range(64)]
    Ps.append(P); print('H',i,'rank',64-K.nrows(),'kernel rows',K.nrows(),flush=True)
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
mu=-g0           # bound exactly 0
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
# numeric G_i
x0=np.zeros(len(var))
for i in range(8):
    Pp=np.linalg.pinv(Pn[i]); G=Pp@Hs[i]@Pp.conj().T; G=(G+G.conj().T)/2; r=G.shape[0]
    print('  G',i,'min eig',np.linalg.eigvalsh(G).min(),flush=True)
    for s in range(r):
        for t in range(s,r):
            x0[vid[(i,'A',s,t)]]=G[s,t].real
            if s<t: x0[vid[(i,'B',s,t)]]=G[s,t].imag
L=np.zeros((len(rows),len(var)))
for k,d_ in enumerate(rows):
    for j,cf in d_.items(): L[k,j]=float(cf)
bn=np.array([float(b) for b in rhs]); print('numeric residual (projected SCS dual)',np.abs(L@x0-bn).max(),'(scale',np.abs(bn).max(),')',flush=True)
# max-margin interior point on the reduced face (Clarabel): max t s.t. L x = b, E_i(x) - t I PSD (real embedding of G_i)
import cvxpy as cp, scipy.sparse as sps
xv=cp.Variable(len(var)); tv=cp.Variable(); cons=[sps.csr_matrix(L)@xv==bn, cp.abs(xv)<=1e3]
for i in range(8):
    r=Pi[i].shape[1]; Ri=[];Ci=[];Vi=[]
    for (ii,kind,s_,t_),j in vid.items():
        if ii!=i: continue
        if kind=='A':
            for (a,b) in {(s_,t_),(t_,s_),(r+s_,r+t_),(r+t_,r+s_)}: Ri.append(a*2*r+b); Ci.append(j); Vi.append(1.0)
        else:   # E = [[A,-B],[B,A]], B[s,t]=x, B[t,s]=-x
            for (a,b,sg) in [(s_,r+t_,-1),(t_,r+s_,1),(r+s_,t_,1),(r+t_,s_,-1)]: Ri.append(a*2*r+b); Ci.append(j); Vi.append(sg)
    Mi=sps.csr_matrix((Vi,(Ri,Ci)),shape=(4*r*r,len(var))); E=cp.reshape(Mi@xv,(2*r,2*r),order='C')
    cons.append((E+E.T)/2-tv*np.eye(2*r)>>0)
try:
    pr=cp.Problem(cp.Maximize(tv),cons); pr.solve(solver='CLARABEL')
    print('max-margin solve',pr.status,'margin t',tv.value,f'{time.time()-t0:.0f}s',flush=True)
    if pr.status=='optimal' and tv.value>1e-9:
        x0=xv.value; print('numeric residual (max-margin point)',np.abs(L@x0-bn).max(),flush=True)
except Exception as ex: print('max-margin solve failed (',type(ex).__name__,'); using the projected SCS dual',flush=True)
# rows/cols to pivot on
from scipy.linalg import qr
_,Rr,pr=qr(L.T,pivoting=True,mode='economic'); rk=int((np.abs(np.diag(Rr))>1e-8*abs(Rr[0,0])).sum()); R_=sorted(pr[:rk])
_,Rc,pc=qr(L[R_],pivoting=True,mode='economic'); Cp=sorted(pc[:rk]); print('rank',rk,flush=True)
xq=[Fr(float(x)).limit_denominator(10**14) for x in x0]
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
          open(f'h24_cert_o{orb}{TAG}.json','w'))
def posdef(Mq):
    m=len(Mq); a=[row[:] for row in Mq]
    for k in range(m):
        if a[k][k]<=0: return False
        for r_ in range(k+1,m):
            fct=a[r_][k]/a[k][k]
            if fct:
                for c_ in range(k,m): a[r_][c_]-=fct*a[k][c_]
    return True
ok=True
for i,(A,B) in enumerate(Gs):
    r=len(A); E=[[A[s][t] for t in range(r)]+[-B[s][t] for t in range(r)] for s in range(r)]+[[B[s][t] for t in range(r)]+[A[s][t] for t in range(r)] for s in range(r)]
    pd=posdef(E); ok&=pd; print('  G',i,'exactly positive definite:',pd,flush=True)
print(f'CHECKER A orbit {orb} facet {f}: certificate {"VALID" if ok else "INVALID"}; bound mu+g0 = {mu+g0}  {time.time()-t0:.0f}s')
