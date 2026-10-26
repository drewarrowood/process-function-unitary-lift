"""Round 21: basin hopping from a saved time-reversed PF-lift point.  usage: params.npy W ORB seed NTRY [save_prefix]
Each try: theta + scale*N(0,1) (scale in 0.03..1), Rayleigh L-BFGS then eigenvalue L-BFGS; keeps the best (exact eigenvalue)."""
import sys, numpy as np, torch, time
pf=sys.argv[1]; W=int(sys.argv[2]); ORB=int(sys.argv[3]); seed=int(sys.argv[4]); NT=int(sys.argv[5]); pre=sys.argv[6] if len(sys.argv)>6 else '/tmp/r21/basin'
src=open('h20_trev_search.py').read().split('rng=np.random')[0]
sys.argv=['x',str(W),'1','1',str(ORB)]; exec(src)
npar,value=build(maxi[W]); f=FAC[ORB]; Tf=torch.tensor(Tn[f,:64].reshape(-1,8,8)); cf=torch.tensor(Tn[f,64])
def EIG(t):
    global MODE
    m=MODE; MODE='eig'; v=value(t,Tf,cf); MODE=m; return float(v)
th0=torch.tensor(np.load(pf)); best=(EIG(th0),th0); print('start',best[0],flush=True)
rng=np.random.default_rng(seed); t0=time.time()
for r in range(NT):
    sc=float(rng.choice([0.03,0.1,0.3,1.0]))
    th=(best[1]+sc*torch.tensor(rng.normal(size=npar))).clone().requires_grad_(True)
    opt=torch.optim.LBFGS([th],max_iter=400,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-15)
    def clo():
        opt.zero_grad(); v=value(th,Tf,cf); v.backward(); return v
    try: opt.step(clo)
    except Exception: continue
    v=EIG(th.detach())
    if v<best[0]-1e-12:
        best=(v,th.detach().clone()); np.save(f'{pre}_w{W}_o{ORB}_s{seed}.npy',best[1].numpy())
    if r%10==0 or v<best[0]+1e-12: print(r,sc,'%.6e'%v,'best %.8e'%best[0],f'{time.time()-t0:.0f}s',flush=True)
print('FINAL best %.10e'%best[0])
