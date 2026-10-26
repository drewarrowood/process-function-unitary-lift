"""Round 22 (H.29.2): penalty search over classical-output pure processes (h22_copp.py) for one facet per orbit.
Params: U_o = expm(i H_o) (8 Hermitian 8x8) and psi.  Objective: Rayleigh quotient of the facet form + mu*pen(U), mu raised
in stages; final stage minimises pen alone (projection onto the valid set), then the exact minimum over psi (smallest
eigenvalue) is reported with the residual pen.  usage: ORBS seed NSTART [scale] [MODE: rand | pb | pbL | fwd  (start from a random valid PF phase board / Lugano-type phase board / forward lift)]"""
import sys, time, numpy as np, torch
from h22_copp import *
from h20_common import Tn, REP, canon
torch.set_num_threads(1)
def herm(x):
    A=torch.complex(x[:,:64].reshape(8,8,8),x[:,64:].reshape(8,8,8)); return (A+A.conj().transpose(1,2))/2
U0=None
def Uof(x):
    U=torch.linalg.matrix_exp(1j*herm(x)); return U if U0 is None else U0@U
def run(Tf,cf,x0,ps0,mus=(1,10,100,1e3,1e4),iters=300):
    x=x0.clone().requires_grad_(True); ps=ps0.clone().requires_grad_(True)
    for mu in mus:
        opt=torch.optim.LBFGS([x,ps],max_iter=iters,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-15)
        def clo():
            opt.zero_grad(); U=Uof(x); psi=torch.complex(ps[:8],ps[8:])
            v=(torch.vdot(psi,facet_M(U,Tf,cf)@psi).real/torch.vdot(psi,psi).real)+mu*pen(U); v.backward(); return v
        opt.step(clo)
    opt=torch.optim.LBFGS([x],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-18)
    def clo2():
        opt.zero_grad(); v=pen(Uof(x)); v.backward(); return v
    opt.step(clo2)
    U=Uof(x.detach()); return float(torch.linalg.eigvalsh(facet_M(U,Tf,cf))[0]), float(pen(U)), x.detach(), ps.detach()
if __name__=='__main__':
    ORBS=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NS=int(sys.argv[3]); sc=float(sys.argv[4]) if len(sys.argv)>4 else 1.0
    MODE=sys.argv[5] if len(sys.argv)>5 else 'rand'; MUS=(1,10,100,1e3,1e4) if MODE=='rand' else (1e2,1e3,1e4)
    rng=np.random.default_rng(seed); t0=time.time()
    import json; from h20_common import B3, others
    E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
    from scipy.stats import unitary_group
    def start_U():
        w=maxi[rng.integers(20)] if MODE!='pbL' else maxi[[4,5,6,7,10,11,14,15][rng.integers(8)]]
        if MODE in ('pb','pbL'):   # random PF phase board with random frames
            t=rng.uniform(0,2*np.pi,(3,2,4)); Fr=[unitary_group.rvs(2,random_state=rng) for k in range(3)]; Ef=np.kron(np.kron(Fr[0],Fr[1]),Fr[2])
            return np.array([Ef@np.diag([np.exp(1j*sum(t[k,B3[o][k],w[k][others(k,a)]] for k in range(3))) for a in range(8)]) for o in range(8)])
        if MODE=='fwd':          # random forward PF lift with qubit node wires
            Us=[[unitary_group.rvs(2,random_state=rng) for x in range(4)] for k in range(3)]
            return np.array([np.kron(np.kron(Us[0][w[0][others(0,o)]],Us[1][w[1][others(1,o)]]),Us[2][w[2][others(2,o)]]) for o in range(8)])
        return None
    for orb in ORBS:
        f=REP[orb] if orb in REP else int(np.where(canon==orb)[0][0])
        Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); best=(9,9,None); hits=0
        for r in range(NS):
            u=start_U(); U0=None if u is None else torch.tensor(u)
            x0=torch.tensor(rng.normal(size=(8,128))*sc*(rng.choice([0.3,1,3]) if u is None else 0.01)); ps0=torch.tensor(rng.normal(size=16))
            try: v,pv,x,ps=run(Tf,cf,x0,ps0,mus=MUS)
            except Exception as e: print('err',e); continue
            ok=pv<1e-12; hits+= ok and v<-1e-7
            if ok and v<best[0]:
                best=(v,pv,x.numpy()); np.save(f'/tmp/r22/copp_{MODE}_o{orb}_s{seed}.npy',Uof(x).numpy())
            print(f'  orb {orb} start {r}: lam {v:.4e} pen {pv:.1e}  {time.time()-t0:.0f}s',flush=True)
        
        print(f'orbit {orb} facet {f}: best lam {best[0]:.6e} (pen {best[1]:.1e}), valid hits {hits}/{NS}, {time.time()-t0:.0f}s',flush=True)
