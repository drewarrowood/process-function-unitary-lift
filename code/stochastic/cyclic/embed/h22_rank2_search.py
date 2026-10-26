"""Round 22 (H.29.2): the time-reversed PF lifts of H.27.2 reduced to their extreme points.  By Lemma H.29.2a the statistics depend
on the lift only through the correlation matrices K_k(o)[x,x'] = <U_{k,x} phi_k(o), U_{k,x'} phi_k(o)> (n_k x n_k, unit diagonal),
and the facet value is affine in each K_k(o) separately, so its minimum is attained at extreme points of the complex elliptope:
rank 1 (= PF phase boards) when n_k <= 3, rank <= 2 when n_k = 4.  Here every K_k(o) is the Gram matrix of n_k unit vectors in C^2
for parties with n_k = 4 (rank <= 2) and of n_k unit vectors in C^1 (phases, rank 1) for n_k <= 3, which contains all extreme points
for every refined PF.  (Using C^2 for every party also contains them, but the optimiser then drifts into the interior: 0/20 hits on orbit 30.)  usage: WLIST seed NSTART [ORBS]"""
import sys, json, time, numpy as np, torch
from h20_common import *
from h21_phase_search import su2
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
def build(parts):
    nb=[max(p)+1 for p in parts]; xa=[torch.tensor([parts[k][others(k,a)] for a in range(8)]) for k in range(3)]
    dk=[2 if nb[k]==4 else 1 for k in range(3)]
    npar=sum(2*nb[k]*2*dk[k] for k in range(3))+9+16
    ik=[torch.tensor([B3[i][k] for i in range(8)]) for k in range(3)]; bits=[[B3[a][k] for a in range(8)] for k in range(3)]
    def G_of(th):
        off=0; G=torch.ones(8,8,8,8,dtype=torch.complex128)    # [i,o,a,b]
        for k in range(3):
            d=dk[k]; v=th[off:off+4*d*nb[k]].reshape(2,nb[k],2*d); off+=4*d*nb[k]
            v=torch.complex(v[...,:d],v[...,d:]); v=v/torch.linalg.norm(v,dim=-1,keepdim=True)   # [o_k, x, 2]
            K=torch.einsum('oxd,oyd->oxy',v.conj(),v)                                            # [o_k, x, x']
            Kk=K[ik[k]][:,xa[k]][:,:,xa[k]]                                                      # [o, a, b]
            G=G*Kk[None]
        for k in range(3):
            Ek=su2(th[off:off+3]); off+=3; ee=Ek[bits[k]][:,ik[k]].T
            G=G*(ee.conj()[:,None,:,None]*ee[:,None,None,:])
        return G, th[off:off+16]
    def value(th,Tf,cf,eig=False):
        G,ps=G_of(th)
        M=torch.einsum('fio,ioab->fab',Tf.to(torch.complex128),G)+cf[:,None,None]*torch.eye(8)
        if eig: return torch.linalg.eigvalsh(M)[:,0].min()
        psi=torch.complex(ps[:8],ps[8:]); return (torch.einsum('a,fab,b->f',psi.conj(),M,psi).real/torch.vdot(psi,psi).real)[0]
    return npar,value
if __name__=='__main__':
    widx=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NS=int(sys.argv[3])
    ORBS=[int(a) for a in sys.argv[4].split(',')] if len(sys.argv)>4 else OPEN
    rng=np.random.default_rng(seed); t0=time.time()
    for wi in widx:
        npar,value=build(maxi[wi]); out={}
        for orb in ORBS:
            f=[REP[orb]] if orb in REP else list(np.where(canon==orb)[0][:1])
            Tf=torch.tensor(Tn[f,:64].reshape(-1,8,8)); cf=torch.tensor(Tn[f,64]); best=9; hits=0
            for r in range(NS):
                th=torch.tensor(rng.normal(size=npar)*rng.choice([0.5,1.0,3.0]),requires_grad=True)
                opt=torch.optim.LBFGS([th],max_iter=200,line_search_fn='strong_wolfe',tolerance_grad=1e-11,tolerance_change=1e-14)
                def clo():
                    opt.zero_grad(); v=value(th,Tf,cf); v.backward(); return v
                try: opt.step(clo)
                except Exception: continue
                v=float(value(th.detach(),Tf,cf,eig=True)); hits+=v<-1e-9; best=min(best,v)
            out[orb]=(best,hits)
        print('w',wi,'blocks',[max(p)+1 for p in maxi[wi]],'best (value, #starts < -1e-9):',{o:('%.4e'%v,h) for o,(v,h) in out.items()},f'{time.time()-t0:.0f}s',flush=True)
