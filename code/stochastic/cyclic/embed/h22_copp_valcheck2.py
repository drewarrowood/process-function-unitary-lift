"""Round 22 (H.29.1): second cross-check: points made valid by minimising the COPP criterion pen alone (general phase
processes with nonzero o_j o_k z_l terms, and general COPP from random unitaries) also have Araujo penalty ~ 0, and their
statistics are valid classical processes (positivity and normalisation under all 64 deterministic interventions are automatic
for p(i|o) = |<i|U_o psi>|^2 with unitary U_o; we check the stronger Araujo condition)."""
import sys; sys.argv=['x','0','0']
import numpy as np, torch
from h22_copp import pen, V_of
import h16_gen_search as H
from h22_phaseproc import U_of
torch.set_num_threads(1)
rng=np.random.default_rng(5)
def herm(x):
    A=torch.complex(x[:,:64].reshape(8,8,8),x[:,64:].reshape(8,8,8)); return (A+A.conj().transpose(1,2))/2
for kind in ['phase']*4+['copp']*3:
    if kind=='phase':
        x=torch.tensor(rng.uniform(-np.pi,np.pi,21),requires_grad=True); f=lambda: pen(U_of(x)); getU=lambda: U_of(x.detach())
    else:
        x=torch.tensor(rng.normal(size=(8,128)),requires_grad=True); f=lambda: pen(torch.linalg.matrix_exp(1j*herm(x))); getU=lambda: torch.linalg.matrix_exp(1j*herm(x.detach()))
    opt=torch.optim.LBFGS([x],max_iter=2000,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
    def clo():
        opt.zero_grad(); v=f(); v.backward(); return v
    opt.step(clo); U=getU()
    extra='' if kind!='phase' else ' o_j o_k z_l coeffs/pi: '+str(np.round(np.mod(x.detach().numpy()[9:12]/np.pi+1,2)-1,4))
    print(f'{kind}: COPP pen {float(pen(U)):.2e}, Araujo pen {float(H.penalty(V_of(U))):.2e}'+extra,flush=True)
