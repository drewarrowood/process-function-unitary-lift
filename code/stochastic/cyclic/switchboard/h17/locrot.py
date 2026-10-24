"""H.17.6 [numerical screen; exact if a hit is found]: locally rotated X-type boards U_o -> L U_o, L = L_A (x) L_B (x) L_C.
A common local left unitary preserves the Pauli rule exactly (it maps 'trivial on party k' to itself), so every L U is pure,
but p changes.  Screen: Z_8 X-type class representatives (h13/xreps_z8.npy; mode z4 = the all-even ones) times the 216
local Clifford cosets L in {I,H,S,HS,SH,HSH}^3, scored on all facets of the 23 never-crossed orbits (max over source states)."""
import sys, json, time
from lib3 import *
mode=sys.argv[1]; sh=int(sys.argv[2]); ns=int(sys.argv[3])
T,canon=load_facets(); sel=np.nonzero(np.isin(canon,NC))[0]; Ts=T[sel]; cs=canon[sel]
B=np.load('../h13/xreps_z8.npy').astype(np.int64)
if mode=='z4': B=B[(B%2==0).all((1,2))]
B=B[sh::ns]
H2=np.array([[1,1],[1,-1]])/2**.5; S2=np.diag([1,1j])
C1=[np.eye(2),H2,H2@S2]   # left cosets of {diagonal} x Pauli in the Clifford group: diagonal left factors leave p unchanged, left Paulis act as orbit symmetries
Ls=[np.kron(np.kron(C1[a],C1[b]),C1[c]) for a in range(3) for b in range(3) for c in range(3)]
Hd=np.array([[(-1)**bin(x&y).count('1') for y in range(8)] for x in range(8)])/8**.5; zeta=np.exp(2j*np.pi/8)
best={o:-1. for o in NC}; arg={}; t0=time.time()
for n,b in enumerate(B):
    U0=np.stack([Hd@np.diag(zeta**b[o])@Hd for o in range(8)])
    for li,L in enumerate(Ls):
        U=np.einsum('ij,ojk->oik',L,U0); P=projectors(U)
        v=-np.linalg.eigvalsh(np.einsum('fr,rst->fst',Ts[:,:64],P)+Ts[:,64,None,None]*np.eye(8))[:,0]
        for o in NC:
            m=v[cs==o].max()
            if m>best[o]: best[o]=float(m); arg[o]=(int(n*ns+sh),li)
    if n%20==0: print(n,len(B),round(time.time()-t0),max(best.values()),flush=True)
print('max over NC orbits:',json.dumps(best)); json.dump(dict(best=best,arg=arg),open('locrot_%s_%d.json'%(mode,sh),'w'))
