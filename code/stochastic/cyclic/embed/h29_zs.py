"""Round 29: zero-set kernels for an h29_export.py problem (any level).  Zeros (psi, xi, u) of p on the reduced family come from
random starts (Adam + L-BFGS on lambda_min(M) + c, as h27_zs.py) or from an .npy of angle rows th = [a(3), t(3), p(3)];
for each zero with lambda_min < 1e-12 and each psi in the (numerical) null space of M + c (eigenvalue < 1e-10), every Gram block
must annihilate the vector of basis monomials evaluated there.  Output npz W{b} rows (as h27_zs.py).
usage: orbit problem.json NSTART|angles.npy seed out.npz"""
import sys, json, time, numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); D=json.load(open(sys.argv[2])); rng=np.random.default_rng(int(sys.argv[4])); t0=time.time()
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
if sys.argv[3].endswith('.npy'): x=torch.tensor(np.load(sys.argv[3]))
else:
    NS=int(sys.argv[3]); th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
    for it_ in range(2500):
        opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
        if it_ in (1200,2000):
            for g_ in opt.param_groups: g_['lr']*=0.1
    x=th.detach().clone().requires_grad_(True); o2=torch.optim.LBFGS([x],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-16,tolerance_change=1e-22)
    def clo():
        o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
    o2.step(clo); x=x.detach()
vv=lam(x,Tf,cf).detach().numpy(); keep=vv<1e-12
print(f'orbit {orb}: {len(vv)} points, kept {keep.sum()} with value < 1e-12 (min {vv.min():.2e})  {time.time()-t0:.0f}s',flush=True)
th=x[keep]; M=Mmat(th,Tf,cf).detach(); ev,U=torch.linalg.eigh(M)
mono=[[np.array(a) for a in m] for m in D['mono']]
A=np.array([m[0] for m in mono]); Ab=np.array([m[1] for m in mono]); Xe=np.array([m[2] for m in mono]); Xb=np.array([m[3] for m in mono]); Dm=np.array([m[4] for m in mono])
rows=[]
for b in range(th.shape[0]):
    a,t,p=th[b,:3].numpy(),th[b,3:6].numpy(),th[b,6:].numpy()
    xi=np.stack([np.cos(t/2),np.sin(t/2)*np.exp(1j*p)],1).reshape(6); u=np.exp(1j*a)
    for j in range(8):
        if ev[b,j]>=1e-10: break
        psi=U[b,:,j].numpy()
        val=np.prod(psi**A,1)*np.prod(np.conj(psi)**Ab,1)*np.prod(xi**Xe,1)*np.prod(np.conj(xi)**Xb,1)*np.prod(u**Dm,1)
        rows.append(val)
V=np.array(rows); print(f'{len(rows)} zero vectors',flush=True)
out={}; tot=0
for bi,bl in enumerate(D['blocks']):
    Wm=V[:,bl['basis']]; out[f'W{bi}']=Wm
    s=np.linalg.svd(np.r_[Wm.real,Wm.imag],compute_uv=False); s=s/max(s[0],1e-300); tot+=len(bl['basis'])-int((s>1e-10).sum())
np.savez_compressed(sys.argv[5],**out)
print(f'real face dimension (threshold 1e-10) {tot} of {sum(len(b["basis"]) for b in D["blocks"])}  {time.time()-t0:.0f}s')
