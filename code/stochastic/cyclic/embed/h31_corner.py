"""Round 31: crossing-witness search at the intersections of the zero components of an orbit (reduced 6-dim family, p = 0 by Lemma H.36.5).
Starts: random points on a pairwise intersection of the five components of 28, perturbed by delta in {1e-3,1e-2,1e-1,0.3}; Adam + L-BFGS on lambda_min.
Also minimises the normalised ratios lambda/(sin^2 t0 sin^2 t1) and lambda/(sin^2 t0 (sin^2(a2/2)+sin^2 t2)) near the corresponding intersections.
usage: orbit NSTART seed"""
import sys, numpy as np, torch
from h24_lugsearch import Mmat
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
orb=int(sys.argv[1]); NS=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]))
f=int(np.where(canon==orb)[0][0]); Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
def lam(th6):
    th=torch.cat([th6,torch.zeros(th6.shape[0],3)],1); return torch.linalg.eigvalsh(Mmat(th,Tf,cf))[:,0]
comps={'s0':{3:0.},'s1':{4:0.},'a2s2':{2:0.,5:0.},'a1a2':{1:0.,2:0.},'a0a2':{0:0.,2:0.}}
names=list(comps); best=[]
for i in range(len(names)):
  for j in range(i+1,len(names)):
    fix={**comps[names[i]],**comps[names[j]]}
    for d in [1e-3,1e-2,1e-1,0.3]:
        th=rng.uniform(-np.pi,np.pi,(NS,6))
        for k,v in fix.items(): th[:,k]=v+rng.choice([0,np.pi],NS)*(k>=3)
        th=th+d*rng.standard_normal((NS,6))
        x=torch.tensor(th,requires_grad=True); opt=torch.optim.Adam([x],lr=min(d,0.05)/5)
        for it in range(800):
            opt.zero_grad(); v=lam(x); v.sum().backward(); opt.step()
        v=lam(x).detach().numpy(); best.append((v.min(),names[i]+'&'+names[j],d))
        print(f'{orb} {names[i]}&{names[j]} delta {d}: min lambda {v.min():.3e}  frac < -1e-10: {(v<-1e-10).mean():.3f}',flush=True)
def ratio(den,label,fix):
    th=rng.uniform(-np.pi,np.pi,(NS,6))
    for k,v in fix.items(): th[:,k]=v
    th=th+0.05*rng.standard_normal((NS,6)); x=torch.tensor(th,requires_grad=True); opt=torch.optim.Adam([x],lr=0.01)
    for it in range(1500):
        opt.zero_grad(); r=lam(x)/(den(x)+1e-12); r.sum().backward(); opt.step()
    r=(lam(x)/den(x)).detach().numpy(); print(f'{orb} min {label}: {r.min():.4e}  (median {np.median(r):.3e})',flush=True)
ratio(lambda x: torch.sin(x[:,3])**2*torch.sin(x[:,4])**2,'lambda/(sin^2 t0 sin^2 t1) near s0&s1',{3:0.,4:0.})
ratio(lambda x: torch.sin(x[:,3])**2*(torch.sin(x[:,2]/2)**2+torch.sin(x[:,5])**2),'lambda/(sin^2 t0 (sin^2 a2/2 + sin^2 t2)) near s0&a2s2',{3:0.,2:0.,5:0.})
print(orb,'overall min lambda',min(best)[0])
