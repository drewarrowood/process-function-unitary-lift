"""Round 24 (H.31.2): purity-based SDP relaxation ("level-2 class lift") for PF phase boards on a Lugano-type rule w' (blocks (2,2,2)).
By Lemma H.29.2a (n_k = 2: elementary) the minimum of any facet over the time-reversed PF lifts on w' is attained at PF phase boards;
after absorbing z-only phases into the source, v_o = D_o psi with D_o = diag(prod_k u_k^{o_k x_k(z)}), |u_k| = 1, x_k(z) = w'_k(z_{-k}).
Statistics p(i|o) = f_i^dag v_o v_o^dag f_i with the product frame vector f_i = (x)_k e_k(i_k).
Lift: X[(o,z),(o',z')] = psi_z conj(psi_z') prod_k u_k^{e_k}, e_k = o_k x_k(z) - o'_k x_k(z')   (64 x 64, PSD);
      Z(i) = diag(1 (x) conj f_i) X diag(1 (x) f_i), i.e. Z(i)[(o,z),(o',z')] = X[..] g_{zz'}(i), g_{zz'}(i) = prod_k conj(e_k[i_k,z_k]) e_k[i_k,z'_k].
Exact properties kept (linear or PSD, so this is a relaxation; mixed sources covered by convexity):
  X, Z(i) PSD; X and each Z(i) constant on the classes c = (z,z',e); sum_z X[(0,z),(0,z)] = 1;
  i -> Z(i)_c lies in the frame span ipat(z,z') (Lemma H.30.1);  sum_i Z(i)_c = X_c when z = z'.
Objective sum_{i,o} T[i,o] sum_{z,z'} Z(i)[(o,z),(o,z')] + c.  A minimum >= 0 proves the facet on the family; < 0 proves nothing.
Solved with SCS through h24_conic.py (Clarabel runs out of memory on nine 128 x 128 cones).   usage: rule orbits [all]"""
import sys, itertools as it, numpy as np, time, scipy.sparse as sps
from h23_span import ipat, MAXI
from h20_common import Tn, canon, B3, others
import h24_conic as C
def classes(wi):
    parts=MAXI[wi]; x=lambda k,z: parts[k][others(k,z)]
    key={}; idx=np.zeros((64,64),int)
    for o,z,op,zp in it.product(range(8),repeat=4):
        e=tuple(B3[o][k]*x(k,z)-B3[op][k]*x(k,zp) for k in range(3))
        idx[8*o+z,8*op+zp]=key.setdefault((z,zp,e),len(key))
    inv={v:k for k,v in key.items()}
    conj=np.array([key[(zp,z,tuple(-t for t in e))] for (z,zp,e) in [inv[c] for c in range(len(key))]])
    return key,inv,idx,conj
class Model:
    def __init__(s,wi):
        s.key,s.inv,s.idx,s.conj=classes(wi); n=len(s.key); s.n=n
        reps=[c for c in range(n) if s.conj[c]>=c]; s.reps=reps
        s.ra={}; s.rb={}; s.sg={}
        # variable layout: 9 matrices (0 = X, 1..8 = Z(i)); per matrix: a for reps, b for non-self reps
        nv=0; s.va=[]; s.vb=[]
        for m in range(9):
            va={}; vb={}
            for c in reps:
                va[c]=nv; nv+=1
                if s.conj[c]!=c: vb[c]=nv; nv+=1
            s.va.append(va); s.vb.append(vb)
        s.nv=nv
        s.rep=lambda c: c if s.conj[c]>=c else s.conj[c]
        s.sgn=lambda c: 1 if s.conj[c]>c else (-1 if s.conj[c]<c else 0)
        # PSD blocks
        s.blocks=[]
        for m in range(9):
            r,cc,v,val=[],[],[],[]
            for a in range(64):
                for b in range(64):
                    c=s.idx[a,b]; rc=s.rep(c); sg=s.sgn(c)
                    if a<=b:
                        r+= [a,64+a]; cc+=[b,64+b]; v+=[s.va[m][rc]]*2; val+=[1,1]
                    if sg!=0:   # top-right block -I : entry (a, 64+b) = -Im X[a,b]
                        r.append(a); cc.append(64+b); v.append(s.vb[m][rc]); val.append(-sg)
            s.blocks.append((128,r,cc,v,val,None))
        # equalities
        rows=[]; 
        def eq(coefs,rhs=0.0): rows.append((coefs,rhs))
        rho=[s.key[(z,z,(0,0,0))] for z in range(8)]; eq({s.va[0][c]:1.0 for c in rho},1.0)
        for (z,zp) in it.product(range(8),repeat=2):
            G=np.array(ipat(z,zp),float); u,sv,vt=np.linalg.svd(G); rk=int((sv>1e-9).sum()); N=vt[rk:]
            cs=[c for (zz,zzp,e),c in s.key.items() if zz==z and zzp==zp and c in s.va[0]]
            for c in cs:
                for part in ('a','b'):
                    V=s.va if part=='a' else s.vb
                    if c not in V[1]: continue
                    for row in N: eq({V[1+i][c]:row[i] for i in range(8) if abs(row[i])>1e-12})
                    if z==zp:
                        d={V[1+i][c]:1.0 for i in range(8)}; d[V[0][c]]=-1.0; eq(d)
        R=[];Cc=[];Vv=[];bb=[]
        for k,(d,rhs) in enumerate(rows):
            for j,x in d.items(): R.append(k); Cc.append(j); Vv.append(x)
            bb.append(rhs)
        s.Aeq=sps.csr_matrix((Vv,(R,Cc)),shape=(len(rows),nv)); s.beq=np.array(bb)
        s.cnt=np.zeros((8,n))
        for o,z,zp in it.product(range(8),repeat=3): s.cnt[o,s.idx[8*o+z,8*o+zp]]+=1
    def facet(s,f,verbose=False):
        T=Tn[f,:64].reshape(8,8); W=T@s.cnt    # [i, class]
        q=np.zeros(s.nv)
        for i in range(8):
            for c in range(s.n): q[s.va[1+i][s.rep(c)]]+=W[i,c]
        sol=C.solve_scs(q,s.Aeq,s.beq,s.blocks,s.nv,verbose=verbose)
        return sol['info']['pobj']+Tn[f,64], sol['info']['status'], sol
if __name__=='__main__':
    wi=int(sys.argv[1]); orbs=[int(a) for a in sys.argv[2].split(',')]; allf=len(sys.argv)>3 and sys.argv[3]=='all'; t0=time.time()
    M=Model(wi); print('rule',wi,'classes',M.n,'vars',M.nv,'eqs',M.Aeq.shape[0],f'built {time.time()-t0:.0f}s',flush=True)
    for o in orbs:
        fs=np.where(canon==o)[0] if allf else [int(np.where(canon==o)[0][0])]
        res=[M.facet(int(f))[:2] for f in fs]; m=min(v for v,s in res)
        print(f'rule {wi} orbit {o}: facets {len(fs)} SDP2 min {m:.6e} below -1e-7: {sum(v<-1e-7 for v,s in res)} statuses {sorted(set(s for v,s in res))} {time.time()-t0:.0f}s',flush=True)
