"""Round 15, item 2 (H.22.2): search the 22 never-crossed facet orbits on generalised Lugano boards.
Board: L_{U_A,U_B,U_C}: |s>_P|o>_AO -> (U_A^{lug_A(o)} x U_B^{lug_B(o)} x U_C^{lug_C(o)})|s>_AI |o>_F (VOKB fleshing-out of the Lugano
routed graph with an arbitrary qubit unitary in each node; L_X,X,X = Lugano, L_X,sqrtX,X ~ H.12), or its transpose (time reverse),
followed by arbitrary local frames on every agent's input and output qubit (6 SU(2) frames).  Frames on P are absorbed by the
source-state maximisation, frames on F are irrelevant.  Purity is checked numerically for the best boards.
Objective: max over facets in the 22 orbits of the max-over-source-states violation (relative, as in H.21.7).  [NUMERICAL]"""
import itertools as it, numpy as np, gzip, sys
from scipy.optimize import minimize
seed=int(sys.argv[1]); nrand=int(sys.argv[2]); nopt=int(sys.argv[3]); rng=np.random.default_rng(seed)
F='../../physics/facets/'
B3=list(it.product((0,1),repeat=3))
PF=np.load('../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
canon=np.load('../switchboard/h13/xviol.npz')['canon'].astype(int)
OPEN22=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81]
import os
if os.environ.get('ORBITS'): OPEN22=[int(x) for x in os.environ['ORBITS'].split(',')]   # restrict the objective (Round 15 follow-up)
sel=np.isin(canon,OPEN22); Ts=Tn[sel]; cs=canon[sel]; print('facets in the 22 orbits:',sel.sum(),flush=True)
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
def su2(t):   # 3 params -> SU(2)
    a,b,c=t; return np.array([[np.cos(a)*np.exp(1j*b),np.sin(a)*np.exp(1j*c)],[-np.sin(a)*np.exp(-1j*c),np.cos(a)*np.exp(-1j*b)]])
def u2(t): return np.exp(1j*t[3])*su2(t[:3])
k3=lambda a,b,c:np.kron(np.kron(a,b),c)
def board(th,rev):
    U=[u2(th[4*j:4*j+4]) for j in range(3)]; fr=[su2(th[12+3*j:15+3*j]) for j in range(6)]
    Lm=np.zeros((64,64),complex)
    for o in range(8):
        e=lug(*B3[o]); g=k3(*[np.linalg.matrix_power(U[j],e[j]) for j in range(3)])
        for s in range(8):
            for i in range(8): Lm[8*i+o,8*o+s]=g[i,s]
    if rev: Lm=Lm.T     # time reverse, read with the same (AI,F)x(AO,P) convention as h12_family.py
    FI=k3(*fr[:3]); FO=k3(*fr[3:])
    return np.kron(FI,np.eye(8))@Lm@np.kron(FO,np.eye(8))   # rows (AI,F), cols (AO,P)
def forms(V):
    W=V.reshape(8,8,8,8); return np.einsum('ifos,ifot->iost',W.conj(),W).reshape(64,8,8)
def viol(th,rev,full=False):
    P=forms(board(th,rev)); Fm=np.einsum('fr,rst->fst',Ts[:,:64],P)+Ts[:,64,None,None]*np.eye(8)
    v=-np.linalg.eigvalsh(Fm)[:,0]
    if full: out=np.full(max(OPEN22)+1,-9.); np.maximum.at(out,cs,v); return out
    return v.max()
best=[]
for r in range(nrand):
    rev=r%2; th=rng.uniform(0,2*np.pi,30); best.append((viol(th,rev),rev,th))
best.sort(key=lambda t:-t[0])
print(f'seed {seed}: {nrand} random boards; best max-violation over the 22 orbits: {[round(b[0],5) for b in best[:5]]}',flush=True)
glob=-9
for v0,rev,th in best[:nopt]:
    res=minimize(lambda t:-viol(t,rev),th,method='Powell',options={'maxiter':4000,'xtol':1e-6,'ftol':1e-10})
    v=-res.fun; glob=max(glob,v)
    print(f'  rev={rev} start {v0:+.5f} -> {v:+.6f}',flush=True)
    if v>1e-7:
        ov=viol(res.x,rev,True); print('   VIOLATED orbits:',[(o,round(ov[o],6)) for o in OPEN22 if ov[o]>1e-7],flush=True)
        np.save(f'/tmp/r15/never22_hit_{seed}{"_"+os.environ["ORBITS"].replace(",","-") if os.environ.get("ORBITS") else ""}.npy',np.r_[rev,res.x])
print(f'NEVER22 seed {seed}: best {glob:+.6f}',flush=True)
