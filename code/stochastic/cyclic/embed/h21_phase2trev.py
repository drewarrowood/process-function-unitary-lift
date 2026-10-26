"""Round 21: convert a phase-board parameter vector (h21_phase_search.py) into the h20_trev_search.py parametrisation
(D_k = 2 n_k node wires, U_{k,x} = exp(i diag(theta_k(0,x), theta_k(1,x), 0, ..)), phi_k(o) = |o>), so that h21_trev_cert.py
and h21_trev_fullcheck.py apply unchanged.  usage: phase.npy W out.npy"""
import sys, json, numpy as np
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
ph=np.load(sys.argv[1]); W=int(sys.argv[2]); parts=maxi[W]; nb=[max(p)+1 for p in parts]
out=[]; off=0; offE=sum(2*n for n in nb)
for k in range(3):
    n=nb[k]; d=2*n; t=ph[off:off+2*n].reshape(2,n); off+=2*n
    for x in range(n):
        h=np.zeros(2*d*d); 
        for o in range(2): h[o*d+o]=t[o,x]
        out.append(h)
    for o in range(2):
        v=np.zeros(2*d); v[o]=1; out.append(v)
    out.append(ph[offE+3*k:offE+3*k+3])
out.append(ph[offE+9:offE+25]); np.save(sys.argv[3],np.concatenate(out))
