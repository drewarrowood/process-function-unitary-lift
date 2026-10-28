"""Round 32 (H.37): local structure of orbit 28 at the corner {sin t0 = 0} & {sin t1 = 0} (NUMERICAL).
At t0 = t1 = 0 the matrix M(a,t) has a 2-dim kernel; with t0 = tau0 e, t1 = tau1 e the two small eigenvalues are O(e^2) and
lambda_1 lambda_2 = kappa(a,t2) tau0^2 tau1^2 e^4 + O(e^5).  We estimate kappa (two radii, two directions), minimise it over (a,t2),
and test its vanishing order at the triple intersections.  usage: orbit N seed"""
import numpy as np, torch, sys
from h24_lugsearch import Mmat
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); N=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
def kap(x,eps=1e-3,r=0.7):   # x: [B,4] = a0,a1,a2,t2 (torch)
    B=x.shape[0]; th=torch.cat([x[:,:3],torch.full((B,1),eps),torch.full((B,1),eps*r),x[:,3:4],torch.zeros(B,3)],1)
    e=torch.linalg.eigvalsh(Mmat(th,Tf,cf))[:,:2]; return e[:,0]*e[:,1]/(eps**4*r*r)
x0=np.c_[rng.uniform(0,2*np.pi,(N,3)),rng.uniform(0,np.pi,(N,1))]
k=kap(torch.tensor(x0)).numpy(); k2=kap(torch.tensor(x0),eps=5e-4,r=1.6).numpy()
print(f'{orb} kappa on {N} random (a,t2): min {k.min():.3e} median {np.median(k):.3e}; radius/direction consistency (rel, median) {np.median(np.abs(k-k2)/np.abs(k)):.2e}',flush=True)
x=torch.tensor(x0[:min(N,400)],requires_grad=True); opt=torch.optim.Adam([x],lr=0.02)
for it in range(1500):
    opt.zero_grad(); v=kap(x); v.sum().backward(); opt.step()
v=kap(x).detach().numpy(); xs=x.detach().numpy()
def dist(p):   # distance (in (a,t2) coords) to the traces of the three other components on the corner
    a=(p[:,:3]+np.pi)%(2*np.pi)-np.pi; t2=p[:,3]%np.pi; dt2=np.minimum(t2,np.pi-t2)
    return np.c_[np.hypot(a[:,2],dt2),np.hypot(a[:,1],a[:,2]),np.hypot(a[:,0],a[:,2])].min(1)
print(f'{orb} minimised kappa (400 starts, Adam 1500): min {v.min():.3e}; minimisers with kappa < 1e-6: {(v<1e-6).sum()}, max distance of those to the traces {dist(xs[v<1e-6]).max() if (v<1e-6).any() else float("nan"):.3e}',flush=True)
# vanishing order of kappa at the traces
for name,fix in [('a2=t2=0',{2:0.,3:0.}),('a1=a2=0',{1:0.,2:0.}),('a0=a2=0',{0:0.,2:0.})]:
    p=np.c_[rng.uniform(0,2*np.pi,(200,3)),rng.uniform(0,np.pi,(200,1))]
    for kk,vv in fix.items(): p[:,kk]=vv
    d=rng.standard_normal((200,4)); d[:,[j for j in range(4) if j not in fix]]=0; d/=np.linalg.norm(d,axis=1,keepdims=True)
    ks=[kap(torch.tensor(p+h*d)).numpy() for h in (1e-1,1e-2)]
    sl=np.log10(np.abs(ks[0])/np.abs(ks[1]))
    print(f'{orb} trace {name}: kappa on trace max |.| {np.abs(kap(torch.tensor(p)).numpy()).max():.2e}; transverse slope (log10 ratio, h 0.1->0.01): median {np.median(sl):.2f} min {sl.min():.2f}; min kappa/h^2 at h=0.01 {(ks[1]/1e-4).min():.3e}',flush=True)
# corner tori t in {0,pi}^3: M is diagonal and a-independent there; vanishing order of lambda_1 along random directions
a=rng.uniform(0,2*np.pi,(2000,3)); tau=rng.standard_normal((2000,3)); tau/=np.linalg.norm(tau,axis=1,keepdims=True)
th0=torch.tensor(np.c_[a,np.zeros((2000,6))]); M0=Mmat(th0,Tf,cf).numpy()
print(f'{orb} corner t=0: max |offdiag M| {np.abs(M0-np.einsum("bii->bi",M0)[:,:,None]*np.eye(8)).max():.1e}; diag spread over a {np.ptp(np.einsum("bii->bi",M0).real,axis=0).max():.1e}; diag {np.round(np.einsum("bii->bi",M0[:1]).real[0],6)}',flush=True)
for eps in (1e-1,3e-2,1e-2):
    e=torch.linalg.eigvalsh(Mmat(torch.tensor(np.c_[a,eps*tau,np.zeros((2000,3))]),Tf,cf)).numpy()[:,:2]
    print(f'{orb} corner t = eps*tau, eps {eps}: lambda1/eps^4 min {(e[:,0]/eps**4).min():.3e} median {np.median(e[:,0]/eps**4):.3e}; lambda2/eps^2 median {np.median(e[:,1]/eps**2):.3e}',flush=True)
