"""Round 25 (H.32.1): the zero set of a facet on the reduced family (PF phase boards on Lugano rule 4, H.31.1) and the
complementary-slackness kernels it forces on any exact certificate of H.31.3.
If g.p+g0 = sum_i <H_i,Z(i)> + mu + g0 with mu+g0 = 0 and H_i >= 0, every board with facet value 0 has <H_i, w_i w_i^dag> = 0, i.e.
H_i w_i = 0, where w_i[(o,z)] = conj f_i[z] (D_o psi)[z]  (index 8*o+z).  So span{w_i over the zero set} is contained in ker H_i.
Zero points are collected by batched Adam + L-BFGS from random starts (h24_lugsearch model); all eigenvectors of M with eigenvalue < tol count.
usage: orbit NSTART seed [facet]   -> h25_zs_o<orbit>.npz (numeric spans; not committed) and a log on stdout"""
import sys, time, numpy as np, torch
from h24_lugsearch import Mmat, lam, X, OB, IB
from h20_common import Tn, canon, B3
torch.set_default_dtype(torch.float64)
def boards(th):
    """th [B,9] -> f [B,i,z] frame vectors, D [B,o,z] phases"""
    a=th[:,0:3]; t=th[:,3:6]; p=th[:,6:9]
    D=torch.exp(1j*torch.einsum('ok,zk,bk->boz',OB,X,a))
    e0=torch.stack([torch.cos(t/2),torch.sin(t/2)*torch.exp(1j*p)],-1); e1=torch.stack([-torch.sin(t/2)*torch.exp(-1j*p),torch.cos(t/2)+0j],-1)
    E=torch.stack([e0,e1],2); f=torch.ones(th.shape[0],8,8,dtype=torch.complex128)
    for k in range(3):
        idx_i=torch.tensor([IB[i][k] for i in range(8)]); idx_z=torch.tensor([B3[z][k] for z in range(8)])
        f=f*E[:,k][:,idx_i][:,:,idx_z]
    return f,D
def zero_vectors(th,Tf,cf,tol):
    """for each parameter row with lambda_min < tol: all w_i for every eigenvector with eigenvalue < tol -> list per i of arrays [*,64]"""
    with torch.no_grad():
        M=Mmat(th,Tf,cf); ev,U=torch.linalg.eigh(M); f,D=boards(th)
    W=[[] for _ in range(8)]
    for b in range(th.shape[0]):
        for j in range(8):
            if ev[b,j]>=tol: break
            psi=U[b,:,j]; v=(D[b]*psi[None,:])            # [o,z]
            for i in range(8): W[i].append((f[b,i].conj()[None,:]*v).reshape(64).numpy())
    return [np.array(w) for w in W]
if __name__=='__main__':
    orb=int(sys.argv[1]); NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
    f=int(sys.argv[4]) if len(sys.argv)>4 else int(np.where(canon==orb)[0][0]); t0=time.time()
    Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
    th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
    for it_ in range(2000):
        opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
        if it_ in (1000,1600):
            for g_ in opt.param_groups: g_['lr']*=0.1
    v=lam(th,Tf,cf).detach().numpy(); print(f'orbit {orb} facet {f}: {NS} starts; min {v.min():.3e}; below 1e-9: {(v<1e-9).sum()}, below 1e-11: {(v<1e-11).sum()}  {time.time()-t0:.0f}s',flush=True)
    sel=np.where(v<1e-9)[0]
    # polish the near-zero points
    x=th[sel].detach().clone().requires_grad_(True); o2=torch.optim.LBFGS([x],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
    def clo():
        o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
    o2.step(clo); vv=lam(x,Tf,cf).detach().numpy(); keep=vv<1e-12
    print(f'polished {len(sel)}: max {vv.max():.2e}; kept (<1e-12) {keep.sum()}; min over all {min(v.min(),vv.min()):.3e}',flush=True)
    W=zero_vectors(x.detach()[keep],Tf,cf,1e-10)
    out={}
    for i in range(8):
        s=np.linalg.svd(W[i],compute_uv=False); s=s/s[0]; r=int((s>1e-4).sum())
        gap=s[r-1]/s[r] if r<len(s) else np.inf
        print(f'  i={i}: {len(W[i])} zero vectors; span rank {r} (gap {gap:.1e}; sv[r-1]={s[r-1]:.1e}, sv[r]={s[r] if r<len(s) else 0:.1e})',flush=True)
        out[f'W{i}']=W[i]
    np.savez_compressed(f'/tmp/r25/h25_zs_o{orb}'+(f'f{f}' if len(sys.argv)>4 else '')+'.npz',**out)
    print(f'done {time.time()-t0:.0f}s')
