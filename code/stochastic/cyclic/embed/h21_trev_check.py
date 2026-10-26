"""Round 21: check / polish a saved H.27.2 best point (time-reversed PF lift).  usage: W ORB SEED [NPOL]
Rebuilds p(i|o)=psi^dag G_io psi at the min eigenvector, checks normalisation + validity (64 local deterministic interventions),
evaluates all 29,344 facets (relative units) and the 1,536 facets of the 10 open orbits, then polishes with L-BFGS (eigen and Rayleigh)."""
import sys, numpy as np, torch
W,ORB,SEED=map(int,sys.argv[1:4]); NPOL=int(sys.argv[4]) if len(sys.argv)>4 else 20
src=open('h20_trev_search.py').read().split('rng=np.random')[0]
sys.argv=['x',str(W),'1','1',str(ORB)]; exec(src)
parts=maxi[W]; npar,value=build(parts)
th0=torch.tensor(np.load(f'h20_trev_best_w{W}_o{ORB}_s{SEED}.npy'))
f=FAC[ORB]; Tf=torch.tensor(Tn[f,:64].reshape(-1,8,8)); cf=torch.tensor(Tn[f,64])
# expose G: re-run the value code with a hook
import types
def getG(theta):
    global MODE
    out={}
    old=torch.einsum
    def hook(eq,*a):
        if eq=='fio,ioab->fab': out['G']=a[1]
        return old(eq,*a)
    torch.einsum=hook; m=MODE; MODE='eig'
    try: value(theta,Tf,cf)
    finally: torch.einsum=old; MODE=m
    return out['G']
def report(th,tag):
    G=getG(th).detach(); M=torch.einsum('fio,ioab->fab',Tf.to(torch.complex128),G)+cf[:,None,None]*torch.eye(8)
    w,v=torch.linalg.eigh(M[0]); psi=v[:,0]
    p=torch.einsum('a,ioab,b->io',psi.conj(),G,psi).real.numpy()
    herm_res=float((G-G.transpose(2,3).conj()).abs().max())
    # validity
    dev=0
    for g in range(64):
        gs=[(g>>(4-2*k))&3 for k in range(3)]   # g_k in 0..3, party0 most significant
        tot=0
        for i in range(8):
            o=sum(((gs[k]>>B3[i][k])&1)<<(2-k) for k in range(3)); tot+=p[i,o]
        dev=max(dev,abs(tot-1))
    allv=Tn[:,:64]@p.reshape(-1)+Tn[:,64]
    opn=np.isin(canon,OPEN)
    print(f'{tag}: lam_min={w[0].item():.10e}  facet(rel)={allv[f[0]]:.10e}  min p={p.min():.2e}  validity dev={dev:.2e}  G herm res={herm_res:.1e}')
    print(f'   min over all facets {allv.min():.6e} (orbit {canon[allv.argmin()]}), over open-orbit facets {allv[opn].min():.6e}; open facets < -1e-9: {int((allv[opn]<-1e-9).sum())}')
    return p, allv
def EIG(t,Tf,cf):
    global MODE
    m=MODE; MODE='eig'; v=value(t,Tf,cf); MODE=m; return v
p,allv=report(th0,'saved')
np.save(f'/tmp/r21/p_w{W}_o{ORB}_s{SEED}.npy',p)
best=(float(EIG(th0,Tf,cf)),th0)
for r in range(NPOL):
    th=(best[1]+ (0 if r==0 else 1e-3*torch.randn(npar))).clone().requires_grad_(True)
    for m in (['ray','eig'] if r==0 else ['ray']):
        MODE=m
        opt=torch.optim.LBFGS([th],max_iter=2000,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-16)
        def clo():
            opt.zero_grad(); v=value(th,Tf,cf); v.backward(); return v
        try: opt.step(clo)
        except Exception as ex: print('fail',ex)
    MODE='ray'
    v=float(EIG(th.detach(),Tf,cf))
    if v<best[0]-1e-12: best=(v,th.detach().clone()); print(' polish',r,v,flush=True)
report(best[1],'polished')
np.save(f'/tmp/r21/trev_pol_w{W}_o{ORB}_s{SEED}.npy',best[1].numpy())
