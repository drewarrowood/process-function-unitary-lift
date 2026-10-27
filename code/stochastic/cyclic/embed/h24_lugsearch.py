"""Round 24 (H.31.5): exhaustive-style search over the whole Lugano-type problem in its exact minimal parametrisation.
By H.31.1 every Lugano-type case (8 components, 8 rules, all time-reversed lifts on them) has, for each facet orbit, the same minimum as
PF phase boards on rule 4 at the orbit's representative facet.  Exact parametrisation (validity automatic): three phases u_k = e^{i a_k},
three frames given by Bloch angles (t_k, p_k) (a frame's remaining phase is absorbed into the source); the source is eliminated exactly:
value = lambda_min( sum_{i,o} T[i,o] D_o^dag |f_i><f_i| D_o ) + c,  D_o = diag(prod_k u_k^{o_k x_k(z)}).
9 real parameters.  Batched Adam from NSTART uniform random starts, then L-BFGS polish of the best 50.  usage: orbits NSTART seed"""
import sys, time, numpy as np, torch
from h23_span import MAXI
from h20_common import Tn, canon, B3, others
torch.set_default_dtype(torch.float64)
import os
RULE=int(os.environ.get("LUGRULE","4"))
X=torch.tensor([[MAXI[RULE][k][others(k,z)] for k in range(3)] for z in range(8)],dtype=torch.float64)   # [z,k]
OB=torch.tensor([[B3[o][k] for k in range(3)] for o in range(8)],dtype=torch.float64)                 # [o,k]
IB=[[B3[i][k] for k in range(3)] for i in range(8)]
def Mmat(th,Tf,cf):
    """th [B,9] -> [B,8,8] Hermitian"""
    a=th[:,0:3]; t=th[:,3:6]; p=th[:,6:9]
    ph=torch.einsum('ok,zk,bk->boz',OB,X,a)                          # phase of D_o at z
    D=torch.exp(1j*ph)                                                # [B,o,z]
    e0=torch.stack([torch.cos(t/2),torch.sin(t/2)*torch.exp(1j*p)],-1)     # [B,k,2]  frame vector for i_k=0
    e1=torch.stack([-torch.sin(t/2)*torch.exp(-1j*p),torch.cos(t/2)+0j],-1)  # orthogonal
    E=torch.stack([e0,e1],2)                                          # [B,k,i,zbit]
    f=torch.ones(th.shape[0],8,8,dtype=torch.complex128)
    for k in range(3):
        idx_i=torch.tensor([IB[i][k] for i in range(8)]); idx_z=torch.tensor([B3[z][k] for z in range(8)])
        f=f*E[:,k][:,idx_i][:,:,idx_z]
    # amplitude <f_i| D_o |psi> -> row vector r_{io}[z] = conj(f_i[z]) D_o[z]
    R=f.conj()[:,:,None,:]*D[:,None,:,:]                              # [B,i,o,z]
    M=torch.einsum('io,bioz,biow->bzw',Tf.to(torch.complex128),R.conj(),R)
    return M+cf*torch.eye(8)
def lam(th,Tf,cf): return torch.linalg.eigvalsh(Mmat(th,Tf,cf))[:,0]
if __name__=='__main__':
    orbs=[int(a) for a in sys.argv[1].split(',')]; NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3])); t0=time.time()
    for orb in orbs:
        f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
        th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9))*np.r_[np.ones(3),np.ones(3),np.ones(3)],requires_grad=True)
        opt=torch.optim.Adam([th],lr=0.05)
        for it_ in range(1500):
            opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
            if it_==1000:
                for g in opt.param_groups: g['lr']=0.005
        v=lam(th,Tf,cf).detach().numpy(); order=np.argsort(v)[:50]; best=[]
        for j in order:
            x=th[j:j+1].detach().clone().requires_grad_(True); o2=torch.optim.LBFGS([x],max_iter=400,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-18)
            def clo():
                o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
            o2.step(clo); best.append((float(lam(x,Tf,cf)),x.detach().numpy()[0]))
        best.sort(key=lambda b:b[0])
        print(f'orbit {orb} facet {f}: starts {NS}; after Adam: below -1e-7: {(v<-1e-7).sum()}, min {v.min():.6e}; polished best {best[0][0]:.9e} params {np.round(best[0][1],4).tolist()}  {time.time()-t0:.0f}s',flush=True)
