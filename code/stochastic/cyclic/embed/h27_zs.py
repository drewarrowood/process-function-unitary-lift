"""Round 27 (H.34.3): zero-set kernels for the symmetry-reduced Hermitian SOS (h27_export.py blocks).
If p - 0*N = sum v^dag Q v exactly, every zero (psi, xi, u) of p forces Q_blk v_blk = 0 for each torus-weight block (the torus orbit
of a zero consists of zeros, so each weight component vanishes separately).  Zeros are sampled as in h25_zeroset.py.
usage: orbit problem.json NSTART seed out.npz   (NSTART<0: |NSTART| exact points per component of the parametrised zero family)"""
import sys, json, time, numpy as np, torch
from h24_lugsearch import Mmat, lam
from h20_common import Tn, canon, B3
import h26_hsos as H
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); D=json.load(open(sys.argv[2])); NS=int(sys.argv[3]); rng=np.random.default_rng(int(sys.argv[4])); TH=1e-6 if NS>0 else 1e-10
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); t0=time.time()
if NS>0:
    th=torch.tensor(rng.uniform(-np.pi,np.pi,(NS,9)),requires_grad=True); opt=torch.optim.Adam([th],lr=0.05)
    for it_ in range(2000):
        opt.zero_grad(); v=lam(th,Tf,cf); v.sum().backward(); opt.step()
        if it_ in (1000,1600):
            for g_ in opt.param_groups: g_['lr']*=0.1
    x=th.detach().clone().requires_grad_(True); o2=torch.optim.LBFGS([x],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
    def clo():
        o2.zero_grad(); l=lam(x,Tf,cf).sum(); l.backward(); return l
    o2.step(clo)
else:   # exact 4-parameter zero family found in H.34.3 (orbit 57): a1=a2=pi, t0=pi/2, t2=0; plus its k0<->k1 swap
    N=-NS; th=np.zeros((2*N,9))
    for c_,(k,l) in enumerate([(0,1),(1,0)]):
        R=th[c_*N:(c_+1)*N]; R[:,k]=rng.uniform(-np.pi,np.pi,N); R[:,l]=np.pi; R[:,2]=np.pi
        R[:,3+k]=np.pi/2; R[:,3+l]=rng.uniform(0,np.pi,N); R[:,5]=0; R[:,6+k]=rng.uniform(-np.pi,np.pi,N); R[:,6+l]=rng.uniform(-np.pi,np.pi,N)
    x=torch.tensor(th); NS=2*N
vv=lam(x,Tf,cf).detach().numpy(); keep=vv<1e-12
print(f'orbit {orb}: {NS} starts, kept {keep.sum()} with value < 1e-12 (min {vv.min():.2e}, max {vv.max():.2e})  {time.time()-t0:.0f}s',flush=True)
th=x.detach()[keep]; M=Mmat(th,Tf,cf).detach(); ev,U=torch.linalg.eigh(M); B=H.basis()
Z=[]
for b in range(th.shape[0]):
    a,t,p=th[b,:3].numpy(),th[b,3:6].numpy(),th[b,6:].numpy()
    xi=np.stack([np.cos(t/2),np.sin(t/2)*np.exp(1j*p)],1); u=np.exp(1j*a)
    for j in range(8):
        if ev[b,j]>=1e-10: break
        Z.append((U[b,:,j].numpy(),xi,u))
print(f'{len(Z)} zero vectors',flush=True)
out={}; tot=0; rk=[]
for bi,bl in enumerate(D['blocks']):
    S=bl['S']; rows=[]
    for psi,xi,u in Z:
        vec=[]
        for idx in bl['basis']:
            w,bb,m=B[idx]; val=psi[w]
            for k in range(3):
                e=xi[k,B3[bb][k]]; val*=np.conj(e) if (S>>k)&1 else e
                val*=u[k]**m[k]
            vec.append(val)
        rows.append(vec)
    Wm=np.array(rows); s=np.linalg.svd(Wm,compute_uv=False); s=s/max(s[0],1e-300); r=int((s>TH).sum())
    gap=(s[r-1]/s[r]) if r<len(s) else np.inf; n=len(bl['basis']); rk.append((n,r)); tot+=n-r
    print(f' block {bi} S={S} wt={bl["wt"]} n={n}: kernel rank {r} (gap {gap:.1e}), face dim {n-r}',flush=True)
    out[f'W{bi}']=Wm
np.savez_compressed(sys.argv[5],**out)
print(f'total face dimension {tot} of {sum(n for n,_ in rk)}; sum face^2 {sum((n-r)**2 for n,r in rk)}  {time.time()-t0:.0f}s')
