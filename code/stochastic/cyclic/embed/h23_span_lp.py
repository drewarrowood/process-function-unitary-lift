"""Round 23 (H.30.1): compare the exact span S (h23_span.py) with sampled statistics, and float LP minima over Valid ∩ S
for the ten orbits.  usage: comp|rule  indices(comma)|all"""
import sys, itertools as it, numpy as np, torch
from scipy.optimize import linprog
from h23_span import *
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
fs=list(it.product(range(4),repeat=3)); oid=lambda b:4*b[0]+2*b[1]+b[2]
Aeq=np.array([np.array([[1 if o==oid([[0,1,B3[i][k],1-B3[i][k]][f[k]] for k in range(3)]) else 0 for o in range(8)] for i in range(8)]).ravel() for f in fs])
ORB=[26,30,31,28,54,57,66,69,75,81]; FAC={o:np.where(canon==o)[0] for o in ORB}
rng=np.random.default_rng(5)
def samp_comp(ci,N=300):
    from h22_phaseproc import U_of
    M=np.array(C[ci]['rows'],float); r=np.linalg.matrix_rank(M); _,_,Vt=np.linalg.svd(M); Nn=Vt[r:].T; P=[]
    for s in range(N):
        x=np.r_[Nn@(rng.uniform(-np.pi,np.pi,Nn.shape[1])*3),rng.uniform(-np.pi,np.pi,9)]; U=U_of(torch.tensor(x)).numpy()
        psi=rng.normal(size=8)+1j*rng.normal(size=8); psi/=np.linalg.norm(psi); a=np.einsum('ois,s->io',U,psi); P.append((np.abs(a)**2).ravel())
    return np.array(P)
def samp_rule(wi,N=300):
    from h22_rank2_search import build
    import h22_rank2_search as R
    npar,value=build(MAXI[wi]); P=[]
    # reuse G_of via closure is not exported; rebuild statistics through the value function on unit facet vectors is costly, so recompute G here
    nb=[max(p)+1 for p in MAXI[wi]]; xa=[[MAXI[wi][k][others(k,a)] for a in range(8)] for k in range(3)]
    for s in range(N):
        G=np.ones((8,8,8,8),complex)
        for k in range(3):
            D=2*nb[k]; v=rng.normal(size=(2,nb[k],D))+1j*rng.normal(size=(2,nb[k],D)); v/=np.linalg.norm(v,axis=-1,keepdims=True)
            K=np.einsum('oxd,oyd->oxy',v.conj(),v); G*=np.array([[[[K[B3[o][k],xa[k][a],xa[k][b]] for b in range(8)] for a in range(8)] for o in range(8)]])
        for k in range(3):
            q,_=np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2)))
            ee=np.array([[q[B3[i][k],B3[a][k]] for a in range(8)] for i in range(8)]); G*=(ee.conj()[:,None,:,None]*ee[:,None,None,:])
        psi=rng.normal(size=8)+1j*rng.normal(size=8); psi/=np.linalg.norm(psi)
        P.append(np.einsum('a,ioab,b->io',psi.conj(),G,psi).real.ravel())
    return np.array(P)
if __name__=='__main__':
    kind=sys.argv[1]; idx=range(len(C) if kind=='comp' else 20) if sys.argv[2]=='all' else [int(a) for a in sys.argv[2].split(',')]
    for ci in idx:
        G=span_gens((lambda z,zp:opat_comp(ci,z,zp)) if kind=='comp' else (lambda z,zp:opat_rule(ci,z,zp))).astype(float)
        Q,sv,_=np.linalg.svd(G.T,full_matrices=False); d=int((sv>1e-9).sum()); Bs=Q[:,:d]
        P=samp_comp(ci) if kind=='comp' else samp_rule(ci); res=np.abs(P.T-Bs@(Bs.T@P.T)).max()
        sv2=np.linalg.svd(P,compute_uv=False); ds=int((sv2>1e-9*sv2[0]).sum())
        out={}
        for o in ORB:
            m=[]
            for f in FAC[o]:
                lp=linprog(Bs.T@Tn[f,:64],A_ub=-Bs,b_ub=np.zeros(64),A_eq=Aeq@Bs,b_eq=np.ones(64),bounds=[(None,None)]*d,method='highs')
                m.append(lp.fun+Tn[f,64] if lp.status==0 else np.nan)
            out[o]=np.nanmin(m)
        print(kind,ci,'dim S',d,'dim sampled span',ds,'sample residual %.1e'%res,' '.join(f'{o}:{v:.3g}' for o,v in out.items()),flush=True)
