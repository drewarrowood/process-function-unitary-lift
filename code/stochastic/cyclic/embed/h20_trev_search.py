"""Round 20 (H.27.2): gradient search over TIME-REVERSED forward PF lifts with qudit node wires [NUMERICAL].
Forward lift V|s>|a> = (x)_k U_{k,w_k(a)}|s> (x) |a>_F with w a refined PF (h20_fwd_enum.json, 20 maximal ones; binary a, settings
x_k in up to 4 blocks), node wire of dimension D_k = 2*n_k (enough for every Gram matrix of the 2*n_k vectors U_{k,x} phi_k(o)).
In V^T the agents read the binary a-wire in an SU(2) frame (outcome i_k) and write phi_k(o_k) on the node wire; the past is F (source
psi on 8 dims).  p(i|o) = psi^dag G_io psi with G_io[a,b] = e_i(a) conj(e_i(b)) prod_k <U_{k,w_k(a)}phi_k(o_k), U_{k,w_k(b)}phi_k(o_k)>.
For each orbit minimise min over the orbit's facets of lambda_min(sum T G + c I) (the family over all 20 w is invariant under the\n384-element group, so this is the orbit's best value in the family)."""
import sys, os, json, time, torch
from h20_common import *
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
widx=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NR=int(sys.argv[3])
ORBS=[int(a) for a in sys.argv[4].split(',')] if len(sys.argv)>4 else OPEN
import os
MODE=os.environ.get('MODE','ray'); TAU=1e-3
FAC={o:(np.where(canon==o)[0] if MODE=='eig' else np.where(canon==o)[0][:1]) for o in ORBS}   # all facets of the orbit (fixed w: the stabiliser of w does not act transitively)
def herm(x,D):
    A=torch.complex(x[:D*D].reshape(D,D),x[D*D:].reshape(D,D)); return (A+A.conj().T)/2
def su2(t):
    a,b,c=t[0],t[1],t[2]
    return torch.stack([torch.stack([torch.cos(a)*torch.exp(1j*b), -torch.sin(a)*torch.exp(-1j*c)]),
                        torch.stack([torch.sin(a)*torch.exp(1j*c), torch.cos(a)*torch.exp(-1j*b)])])
def build(parts):
    nb=[max(p)+1 for p in parts]; D=[int(os.environ['QD']) if os.environ.get('QD') else 2*n for n in nb]   # QD=2: qubit node wires only
    sizes=[nb[k]*2*D[k]*D[k]+2*2*D[k]+3 for k in range(3)]
    xa=[[parts[k][others(k,a)] for a in range(8)] for k in range(3)]
    def value(theta,Tf,cf):
        off=0; gram=[]; E=[]
        for k in range(3):
            n=nb[k]; d=D[k]; th=theta[off:off+sizes[k]]; off+=sizes[k]
            U=[torch.linalg.matrix_exp(1j*herm(th[2*d*d*x:2*d*d*(x+1)],d)) for x in range(n)]
            ph=th[2*d*d*n:2*d*d*n+4*d]; phi=[torch.complex(ph[4*0*0+2*d*o:2*d*o+d],ph[2*d*o+d:2*d*o+2*d]) for o in range(2)]
            phi=[v/torch.linalg.norm(v) for v in phi]
            vec=torch.stack([torch.stack([U[x]@phi[o] for x in range(n)]) for o in range(2)])   # [o,x,d]
            gx=torch.einsum('oxd,oyd->oxy',vec.conj(),vec)                                       # [o,x,y]
            ga=gx[:,xa[k]][:,:,xa[k]]                                                            # [o,a,b]
            gram.append(ga); E.append(su2(th[-3:]))                                              # E[:,i] basis vector for outcome i
        bits=[[B3[a][k] for a in range(8)] for k in range(3)]
        G=torch.ones(8,8,8,8,dtype=torch.complex128)   # [i,o,a,b]
        for k in range(3):
            e=E[k][bits[k]]          # [a, i_k]  amplitude <a_k|e(i_k)>
            ik=torch.tensor([B3[i][k] for i in range(8)]); ok=torch.tensor([B3[o][k] for o in range(8)])
            ee=e[:,ik].T              # [i,a]
            G=G*(ee.conj()[:,None,:,None]*ee[:,None,None,:])*gram[k][ok][None]
        M=torch.einsum('fio,ioab->fab',Tf.to(torch.complex128),G)+cf[:,None,None]*torch.eye(8)
        if MODE=='eig': return torch.linalg.eigvalsh(M)[:,0].min()
        psi=torch.complex(theta[off:off+8],theta[off+8:off+16])   # smooth Rayleigh quotient (avoids the eigenvalue plateau)
        r=torch.einsum('a,fab,b->f',psi.conj(),M,psi).real/torch.vdot(psi,psi).real
        return -TAU*torch.logsumexp(-r/TAU,0) if r.numel()>1 else r[0]
    return sum(sizes)+16,value
rng=np.random.default_rng(seed); t0=time.time()
for wi in widx:
    parts=maxi[wi]; npar,value=build(parts); out={}
    def EIG(t,Tf,cf):   # report the exact min over source states (eigenvalue), not the Rayleigh quotient
        global MODE
        m=MODE; MODE='eig'; v=value(t,Tf,cf); MODE=m; return v
    for orb in ORBS:
        f=FAC[orb]; Tf=torch.tensor(Tn[f,:64].reshape(-1,8,8)); cf=torch.tensor(Tn[f,64]); best=(9,None)
        for r in range(NR):
            th=torch.tensor(rng.normal(size=npar)*rng.choice([0.3,1.0,3.0]),requires_grad=True)
            opt=torch.optim.LBFGS([th],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-14)
            def clo():
                opt.zero_grad(); v=value(th,Tf,cf); v.backward(); return v
            try: opt.step(clo)
            except Exception as ex: continue
            v=float(EIG(th.detach(),Tf,cf))
            if v<best[0]: best=(v,th.detach().numpy().copy())
        out[orb]=best[0]; np.save(f'h20_trev_best_w{wi}_o{orb}_s{seed}.npy',best[1])
    print('w',wi,maxi[wi],'blocks',[max(p)+1 for p in parts],' min rel. facet value per orbit:',{o:round(v,8) for o,v in out.items()},f'{time.time()-t0:.0f}s',flush=True)
