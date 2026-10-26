"""Round 21 (H.28.2): PF lifts with MIXED forward/time-reversed wiring and GENERAL local instruments [NUMERICAL search].
Forward lift of a refined PF w (h20_fwd_enum.json maximal): V[n,f; s,a] = delta_{f,a} prod_k U_{k,w_k(a_{-k})}[n_k, s_k].
Each party k is wired forward (k receives the node wire n_k, dimension D_k, and emits the binary wire a_k) or time-reversed
(k receives a_k and emits n_k; its s_k goes to the future and its f_k comes from the past).  Contracting V with the agents' Kraus
operators gives, with a = (a_k) the binary label carried by the copy register,
   M[fut; past] = sum_a prod_k Q_k(a)[fut_k, past_k],
   forward k:   Q_k(a)[c, s] = [c = a_k] (A_k U_{k,x})[a_k, s]      (fut_k = c binary, past_k = s in D_k)
   reversed k:  Q_k(a)[s, c] = [c = a_k] (U_{k,x}^T B_k)[s, a_k]    (fut_k = s in D_k, past_k = c binary)
with x = w_k(a_{-k}).  A_k = A_k^{(i_k,o_k,j)} : C^{D_k} -> C^2 and B_k : C^2 -> C^{D_k} are the Kraus operators of an arbitrary
measure-and-prepare instrument: an o-INDEPENDENT measurement with quantum memory, Y_k: C^{d_in} -> C^2(i) (x) C^{d_in}(m), followed
by a preparation channel that depends on the setting o_k AND the outcome i_k, Z_{k,i,o}: C^{d_in}(m) -> C^{d_out} (x) C^L (Kraus
index j < L); isometries are first columns of QR factors.  (The measurement must not depend on o, otherwise o = g(i) is circular
and the induced p is not a classical process.)  p(i|o) = sum_j |M_{i,o,j} psi|^2.
Mode R = set of reversed parties (bitmask 0..7).  R = 0 is the forward family of H.27.1 (a check: it cannot cross); R = 7 contains
H.27.2.  We minimise the Rayleigh quotient of the orbit's representative facet (exact eigenvalue reported).
Usage: python h21_inst_search.py WLIST RLIST seed NSTART [ORBITS] [L]"""
import sys, os, json, time, torch, numpy as np
from h20_common import *
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
WL=[int(a) for a in sys.argv[1].split(',')]; RL=[int(a) for a in sys.argv[2].split(',')]; seed=int(sys.argv[3]); NR=int(sys.argv[4])
ORBS=[int(a) for a in sys.argv[5].split(',')] if len(sys.argv)>5 and sys.argv[5] else OPEN
L=int(sys.argv[6]) if len(sys.argv)>6 else 2; J=L
FAC={o:int(np.where(canon==o)[0][0]) for o in ORBS}
def isom(x,rows,cols):   # rows x cols isometry from 2*rows*cols reals
    A=torch.complex(x[:rows*cols].reshape(rows,cols),x[rows*cols:].reshape(rows,cols)); Q,R=torch.linalg.qr(A)
    return Q*torch.sgn(torch.diagonal(R))[None,:]
def herm(x,D):
    A=torch.complex(x[:D*D].reshape(D,D),x[D*D:].reshape(D,D)); return (A+A.conj().T)/2
def build(parts,R):
    nb=[max(p)+1 for p in parts]; D=[2*n for n in nb]; rev=[(R>>k)&1 for k in range(3)]
    din=[2 if rev[k] else D[k] for k in range(3)]; dout=[D[k] if rev[k] else 2 for k in range(3)]
    Jm=[din[k] for k in range(3)]                       # measurement memory = a copy of the whole input space
    Lk=[max(L,-(-Jm[k]//dout[k])) for k in range(3)]   # Kraus rank of the preparation channel (at least what an isometry needs)
    szY=[2*(2*Jm[k])*din[k] for k in range(3)]; szZ=[2*(dout[k]*Lk[k])*Jm[k] for k in range(3)]
    sz=[nb[k]*2*D[k]*D[k] + szY[k] + 4*szZ[k] for k in range(3)]
    past=[2 if rev[k] else D[k] for k in range(3)]; fut=[D[k] if rev[k] else 2 for k in range(3)]
    NP=int(np.prod(past))
    xa=[[parts[k][others(k,a)] for a in range(8)] for k in range(3)]
    def Q(th,k):
        d=D[k]; n=nb[k]
        U=torch.stack([torch.linalg.matrix_exp(1j*herm(th[2*d*d*x:2*d*d*(x+1)],d)) for x in range(n)])   # [x,d,d]
        off=2*d*d*n
        Y=isom(th[off:off+szY[k]],2*Jm[k],din[k]).reshape(2,Jm[k],din[k]); off+=szY[k]          # measurement: [i,m,in]
        Z=torch.stack([torch.stack([isom(th[off+szZ[k]*(2*i+o):off+szZ[k]*(2*i+o+1)],dout[k]*Lk[k],Jm[k]).reshape(dout[k],Lk[k],Jm[k])
                       for o in range(2)]) for i in range(2)])                                    # preparation: [i,o,out,l,m]
        Y=torch.einsum('iocjm,imx->iojcx',Z,Y)                                                   # Kraus [i,o,l,out,in]
        Ua=U[xa[k]]          # [a,d,d]
        ak=torch.tensor([B3[a][k] for a in range(8)])
        q=torch.zeros(2,2,Lk[k],8,fut[k],past[k],dtype=torch.complex128)
        if rev[k]:   # (U^T B)[s, a_k] : B = Y[i,o,j] : C^2 -> C^D
            T=torch.einsum('axs,iojxc->iojasc',Ua,Y)          # U^T[s,x] = U[x,s]
            for a in range(8): q[:,:,:,a,:,ak[a]]=T[:,:,:,a,:,ak[a]]
        else:        # (A U)[a_k, s] : A = Y : C^D -> C^2
            T=torch.einsum('iojcx,axs->iojacs',Y,Ua)
            for a in range(8): q[:,:,:,a,ak[a],:]=T[:,:,:,a,ak[a],:]
        return q
    def value(theta,Tf,cf,eig=False):
        off=0; qs=[]
        for k in range(3): qs.append(Q(theta[off:off+sz[k]],k)); off+=sz[k]
        M=torch.einsum('ABJaxp,CDKayq,EFLazr->ACEBDFJKLxyzpqr',*qs).reshape(8,8,int(np.prod(Lk)),int(np.prod(fut)),NP)   # [i,o,j,fut,past]
        G=torch.einsum('iojfp,iojfq->iopq',M.conj(),M)          # p(i|o) = psi^dag G psi
        Mf=torch.einsum('io,iopq->pq',Tf.to(torch.complex128),G)+cf*torch.eye(NP)
        if eig: return torch.linalg.eigvalsh(Mf)[0], G
        psi=torch.complex(theta[off:off+NP],theta[off+NP:off+2*NP])
        return (torch.vdot(psi,Mf@psi).real/torch.vdot(psi,psi).real), None
    return sum(sz)+2*NP,value
if __name__=='__main__':
    rng=np.random.default_rng(seed); t0=time.time()
    for wi in WL:
        for R in RL:
            npar,value=build(maxi[wi],R); out={}
            for orb in ORBS:
                f=FAC[orb]; Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); best=(9,None)
                for r in range(NR):
                    th=torch.tensor(rng.normal(size=npar)*rng.choice([0.3,1.0,3.0]),requires_grad=True)
                    opt=torch.optim.LBFGS([th],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-14)
                    def clo():
                        opt.zero_grad(); v=value(th,Tf,cf)[0]; v.backward(); return v
                    try: opt.step(clo)
                    except Exception as ex: continue
                    v=float(value(th.detach(),Tf,cf,eig=True)[0])
                    if v<best[0]: best=(v,th.detach().numpy().copy())
                out[orb]=best[0]
                if best[0]<-1e-6: np.save(f'/tmp/r21/inst_w{wi}_R{R}_o{orb}_s{seed}.npy',best[1])
            print('w',wi,'R',R,'L',L,' min rel. facet value per orbit:',{o:float('%.3e'%v) for o,v in out.items()},f'{time.time()-t0:.0f}s',flush=True)
