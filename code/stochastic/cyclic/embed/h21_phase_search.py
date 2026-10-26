"""Round 21 (H.28.1): the 'phase board' subfamily of time-reversed PF lifts, found to be the structure of the orbit-26 crossing.
For a refined PF w' with binary-coloured blocks, take qubit node wires (QD=2), phi_k(o)=|o>, U_{k,x}=diag phases.  Then the agent's
prepared vectors U_{k,x}phi_k(o) are orthogonal across o and differ only by a phase across x, and
    p(i|o) = psi^dag G_io psi,  G_io[a,b] = prod_k conj(E_k[a_k,i_k]) E_k[b_k,i_k] * exp(i(Phi_o(b)-Phi_o(a))),
    Phi_o(a) = sum_k theta_k(o_k, w'_k(a_{-k}))   (theta_k(o,x): one real phase per output and block; w.l.o.g. theta_k(o,0)=0).
i.e. a diagonal unitary D_o = exp(i Phi_o) on the shared 3-qubit source, then local frames.  usage: WLIST seed NSTART [ORBS]"""
import sys, json, time, numpy as np, torch
from h20_common import *
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
def su2(t):
    a,b,c=t[0],t[1],t[2]
    return torch.stack([torch.stack([torch.cos(a)*torch.exp(1j*b), -torch.sin(a)*torch.exp(-1j*c)]),
                        torch.stack([torch.sin(a)*torch.exp(1j*c), torch.cos(a)*torch.exp(-1j*b)])])
def build(parts):
    nb=[max(p)+1 for p in parts]; xa=[torch.tensor([parts[k][others(k,a)] for a in range(8)]) for k in range(3)]
    npar=sum(2*nb[k] for k in range(3))+9+16
    ik=[torch.tensor([B3[i][k] for i in range(8)]) for k in range(3)]; bits=[[B3[a][k] for a in range(8)] for k in range(3)]
    def G_of(theta):
        off=0; Phi=torch.zeros(8,8)   # [o,a]
        for k in range(3):
            t=theta[off:off+2*nb[k]].reshape(2,nb[k]); off+=2*nb[k]
            Phi=Phi+t[ik[k]][:,xa[k]]            # theta_k(o_k, w_k(a_{-k}))
        ph=torch.exp(1j*Phi)
        G=(ph.conj()[None,:,:,None]*ph[None,:,None,:]).expand(8,8,8,8).clone()
        for k in range(3):
            Ek=su2(theta[off:off+3]); off+=3
            ee=Ek[bits[k]][:,ik[k]].T                  # [i,a]
            G=G*(ee.conj()[:,None,:,None]*ee[:,None,None,:])
        return G, theta[off:off+16]
    def value(theta,Tf,cf,eig=False):
        G,ps=G_of(theta)
        M=torch.einsum('fio,ioab->fab',Tf.to(torch.complex128),G)+cf[:,None,None]*torch.eye(8)
        if eig: return torch.linalg.eigvalsh(M)[:,0].min()
        psi=torch.complex(ps[:8],ps[8:]); return (torch.einsum('a,fab,b->f',psi.conj(),M,psi).real/torch.vdot(psi,psi).real)[0]
    return npar,value,G_of
if __name__=='__main__':
    widx=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NS=int(sys.argv[3])
    ORBS=[int(a) for a in sys.argv[4].split(',')] if len(sys.argv)>4 else OPEN
    rng=np.random.default_rng(seed); t0=time.time()
    for wi in widx:
        npar,value,_=build(maxi[wi]); out={}
        for orb in ORBS:
            f=[REP[orb]] if orb in REP else list(np.where(canon==orb)[0][:1])
            Tf=torch.tensor(Tn[f,:64].reshape(-1,8,8)); cf=torch.tensor(Tn[f,64]); best=(9,None); hits=0
            for r in range(NS):
                th=torch.tensor(rng.normal(size=npar)*rng.choice([0.5,1.0,3.0]),requires_grad=True)
                opt=torch.optim.LBFGS([th],max_iter=200,line_search_fn='strong_wolfe',tolerance_grad=1e-11,tolerance_change=1e-14)
                def clo():
                    opt.zero_grad(); v=value(th,Tf,cf); v.backward(); return v
                try: opt.step(clo)
                except Exception: continue
                v=float(value(th.detach(),Tf,cf,eig=True)); hits+=v<-1e-9
                if v<best[0]: best=(v,th.detach().numpy().copy())
            out[orb]=(best[0],hits); np.save(f'/tmp/r21/phase_w{wi}_o{orb}_s{seed}.npy',best[1])
        print('w',wi,'blocks',[max(p)+1 for p in maxi[wi]],'best (value, #starts < -1e-9):',{o:('%.4e'%v,h) for o,(v,h) in out.items()},f'{time.time()-t0:.0f}s',flush=True)
