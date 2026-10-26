"""Round 22 (H.29.1): cross-check of the COPP validity criterion (h22_copp.pen) against the Araujo projector penalty (h16_gen_search.penalty)
on a certified-type phase board (orbit 30), random unitaries and separable non-PF phases."""
import sys; sys.argv=['x','0','0']
import numpy as np, torch, json
from h22_copp import *
import h16_gen_search as H
from h21_phase_search import build, maxi
rng=np.random.default_rng(0)
# (a) phase board as COPP: U_o = E^dag D_o  (agent measures in frame E)
npar,value,G_of=build(maxi[4])
th=torch.tensor(np.load('h21_phase_best_w4_o30.npy'))
# rebuild D_o and frames directly
from h20_common import B3, others
parts=maxi[4]; nb=[max(p)+1 for p in parts]
off=0; Phi=np.zeros((8,8))
for k in range(3):
    t=th[off:off+2*nb[k]].numpy().reshape(2,nb[k]); off+=2*nb[k]
    for o in range(8):
        for a in range(8): Phi[o,a]+=t[B3[o][k], parts[k][others(k,a)]]
from h21_phase_search import su2
Es=[su2(th[off+3*k:off+3*k+3]).numpy() for k in range(3)]; psi=th[off+9:off+25].numpy(); psi=psi[:8]+1j*psi[8:]
E=np.kron(np.kron(Es[0],Es[1]),Es[2])
U=torch.tensor(np.array([E.T@np.diag(np.exp(1j*Phi[o])) for o in range(8)]))
print('phase board (w4,o30): my pen',float(pen(U)),' Araujo pen',float(H.penalty(V_of(U))))
from h20_common import Tn, REP
f=REP[30]; Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64])
print(' lambda_min',float(torch.linalg.eigvalsh(facet_M(U,Tf,cf))[0]))
# (b) random unitaries
for r in range(3):
    U=torch.linalg.matrix_exp(1j*torch.tensor(np.array([ (lambda A:(A+A.conj().T)/2)(rng.normal(size=(8,8))+1j*rng.normal(size=(8,8))) for o in range(8)])))
    print('random: my pen',float(pen(U)),' Araujo',float(H.penalty(V_of(U))))
# (c) non-PF separable phases: theta_k(o_k, a_{-k}) arbitrary
for r in range(3):
    t=rng.normal(size=(3,2,4)); Phi=np.array([[sum(t[k,B3[o][k],others(k,a)] for k in range(3)) for a in range(8)] for o in range(8)])
    U=torch.tensor(np.array([np.diag(np.exp(1j*Phi[o])) for o in range(8)]))
    print('separable non-PF phases: my pen',float(pen(U)),' Araujo',float(H.penalty(V_of(U))))
# (d) PF permutation lift (Lugano)
