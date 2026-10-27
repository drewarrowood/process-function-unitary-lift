"""Round 26 (H.33): Hermitian decomposable (PPT-type) sum-of-squares relaxation of the reduced family.
p(psi,xi,u) = sum_{i,o} T[i,o] |<f_i(xi)|D_o(u) psi>|^2 + c |psi|^2 prod_k |xi_k|^2   (spinors xi_k, |u_k|=1),
f_i = (x)_k e_{i_k},  e_0 = xi_k,  e_1 = (-conj xi_k1, conj xi_k0).  min over unit psi, xi of p = min of the facet value.
Certificate: p - g |psi|^2 prod|xi_k|^2 = sum_{S subset {0,1,2}} v_S^dag Q_S v_S,  Q_S >= 0,  identity as Laurent polynomials in u
(only |u_k|=1 used), where v_S has entries psi_w * prod_{k notin S} xi_{k,b_k} * prod_{k in S} conj(xi_{k,b_k}) * u^m.
Sound: any feasible g is a lower bound on the minimum.  Basis: m in {0..x_k(w)} (default) or all of {0,1}^3 (MB=full).
usage: orbits   (env MB, EPS, NB = comma list of blocks S as bitmasks, default all 8)"""
import sys, os, time, itertools as it, numpy as np, scipy.sparse as sp, cvxpy as cp
from h23_span import MAXI
from h20_common import Tn, canon, B3, others
X=np.array([[MAXI[4][k][others(k,z)] for k in range(3)] for z in range(8)])
sgn=lambda b: -1 if b==0 else 1
def poly(T,c):
    P={}
    for i in range(8):
        for o in range(8):
            if T[i,o]==0: continue
            ob=np.array(B3[o]); ib=B3[i]
            for z in range(8):
                for w in range(8):
                    xi=[];xb=[];s=1
                    for k in range(3):
                        zk,wk=B3[z][k],B3[w][k]
                        if ib[k]==0: xi.append(zk); xb.append(wk)
                        else: xi.append(1-wk); xb.append(1-zk); s*=sgn(zk)*sgn(wk)
                    d=tuple(ob*X[w]-ob*X[z]); key=(z,w,tuple(xi),tuple(xb),d)
                    P[key]=P.get(key,0)+s*T[i,o]
    N={}
    for z in range(8):
        for a in range(8):
            key=(z,z,B3[a],B3[a],(0,0,0)); N[key]=1.0; P[key]=P.get(key,0)+c
    return P,N
def basis():
    full=os.environ.get('MB','')=='full'; B=[]
    for w in range(8):
        ms=list(it.product((0,1),repeat=3)) if full else list(it.product(*[range(X[w][k]+1) for k in range(3)]))
        for b in range(8):
            for m in ms: B.append((w,b,m))
    return B
def solve(T,c,blocks=range(8),eps=1e-8):
    P,N=poly(T,c); B=basis(); n=len(B); keys={}; rows=[];cols=[];bl=[]
    def kid(k):
        if k not in keys: keys[k]=len(keys)
        return keys[k]
    for S in blocks:
        R=[];C=[]
        for r,(z,a,m) in enumerate(B):
            for s_,(w,b,mp) in enumerate(B):
                xi=[];xb=[]
                for k in range(3):
                    ak,bk=B3[a][k],B3[b][k]
                    if (S>>k)&1: xi.append(ak); xb.append(bk)
                    else: xi.append(bk); xb.append(ak)
                d=tuple(np.array(mp)-np.array(m)); R.append(kid((z,w,tuple(xi),tuple(xb),d))); C.append(r+n*s_)
        bl.append((R,C))
    for k in list(P)+list(N): kid(k)
    K=len(keys); Qs=[cp.Variable((n,n),hermitian=True) for _ in blocks]; g=cp.Variable()
    bvec=np.zeros(K,complex); nv=np.zeros(K)
    for k,v in P.items(): bvec[keys[k]]+=v
    for k,v in N.items(): nv[keys[k]]+=v
    lhs=0
    for Q,(R,C) in zip(Qs,bl):
        A=sp.csr_matrix((np.ones(len(R)),(R,C)),shape=(K,n*n)); lhs=lhs+A@cp.vec(Q,order='F')
    cons=[lhs==bvec-g*nv]+[Q>>0 for Q in Qs]
    pr=cp.Problem(cp.Maximize(g),cons); t0=time.time()
    pr.solve(solver='SCS',eps=eps,max_iters=int(os.environ.get('MAXIT','200000')),verbose=False)
    return n,K,pr.status,g.value,time.time()-t0,Qs
if __name__=='__main__':
    blocks=[int(b) for b in os.environ.get('NB','0,1,2,3,4,5,6,7').split(',')]
    for orb in [int(a) for a in sys.argv[1].split(',')]:
        f=int(np.where(canon==orb)[0][0]); T=Tn[f,:64].reshape(8,8); c=float(Tn[f,64])
        n,K,st,g,t,_=solve(T,c,blocks,float(os.environ.get('EPS','1e-8')))
        print(f'orbit {orb} facet {f} MB={os.environ.get("MB","x")} blocks={blocks}: basis {n}/block, keys {K}, {st}, gamma* = {g}  {t:.0f}s',flush=True)
