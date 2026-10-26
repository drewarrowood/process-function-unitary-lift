"""Round 21 (H.28.2): general DIAGONAL-PHASE boards (beyond refined-PF phase boards), validity by penalty.
V |t>_AO |f>_P = e^{i Phi(t,f)} |f>_AI |t>_F with an ARBITRARY phase function Phi on 64 values, then SU(2) frames on AI.
The phase boards of H.28.1 are the case Phi(t,f) = sum_k theta_k(t_k, w'_k(f_{-k})).  Validity of Tr_F|V>><<V| is imposed by the
Araujo et al. projector penalty (h16_gen_search.penalty), continuation in mu; reported: best facet value with residual.
usage: seed NSTART ORBS"""
import sys, time, numpy as np, torch
seed=int(sys.argv[1]); NS=int(sys.argv[2]); ORBS=[int(a) for a in sys.argv[3].split(',')]
sys.argv=[sys.argv[0],'0','0']
from h16_gen_search import penalty
from h20_common import B3, Tn, canon, REP
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)
def su2(t):
    a,b,c=t[0],t[1],t[2]
    return torch.stack([torch.stack([torch.cos(a)*torch.exp(1j*b), -torch.sin(a)*torch.exp(-1j*c)]),
                        torch.stack([torch.sin(a)*torch.exp(1j*c), torch.cos(a)*torch.exp(-1j*b)])])
eye8=torch.eye(8,dtype=torch.complex128)
def board(th):
    Phi=th[:64].reshape(8,8)                     # [t,f]
    E=[su2(th[64+3*k:67+3*k]) for k in range(3)]
    ET=torch.kron(torch.kron(E[0].T,E[1].T),E[2].T)        # [i,f]
    V=torch.einsum('if,tf,st->istf',ET,torch.exp(1j*Phi).to(torch.complex128),eye8).reshape(64,64)   # rows 8i+s, cols 8t+f
    return V
def V0(th): return torch.einsum('tf,if,st->istf',torch.exp(1j*th[:64].reshape(8,8)).to(torch.complex128),eye8,eye8).reshape(64,64)
def facet(V,psi,Tf,cf):
    Wt=V.reshape(8,8,8,8); P=torch.einsum('ifos,ifot->iost',Wt.conj(),Wt).reshape(64,8,8)
    M=torch.einsum('r,rab->ab',Tf.to(torch.complex128),P)+cf*eye8
    return M
rng=np.random.default_rng(seed); t0=time.time()
for orb in ORBS:
    f=REP[orb]; Tf=torch.tensor(Tn[f,:64]); cf=float(Tn[f,64]); res=[]
    for r in range(NS):
        th=torch.tensor(np.r_[rng.uniform(0,2*np.pi,64),rng.normal(size=9),rng.normal(size=16)],requires_grad=True)
        for mu in (1.,10.,100.,1e3,1e4,1e5):
            opt=torch.optim.LBFGS([th],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-12,tolerance_change=1e-15)
            def clo():
                opt.zero_grad(); psi=torch.complex(th[73:81],th[81:89]); M=facet(board(th),psi,Tf,cf)
                v=(psi.conj()@M@psi).real/(psi.conj()@psi).real + mu*penalty(V0(th)); v.backward(); return v
            try: opt.step(clo)
            except Exception: break
        with torch.no_grad():
            pen=float(penalty(V0(th))); lam=float(torch.linalg.eigvalsh(facet(board(th),None,Tf,cf))[0])
        res.append((lam,pen)); 
        if lam<-1e-6: np.save(f'/tmp/r21/diag_o{orb}_s{seed}_r{r}.npy',th.detach().numpy())
    res=sorted(res); good=[x for x in res if x[1]<1e-12]
    print('orbit',orb,'best (value, residual):',['%.4e/%.1e'%x for x in res[:4]],' best with residual<1e-12:',('%.4e/%.1e'%good[0]) if good else None,f'{time.time()-t0:.0f}s',flush=True)
