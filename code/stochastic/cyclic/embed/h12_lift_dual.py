"""Round 14, item 2: dual of the lifted-A relaxation (h12_lift.py), solved numerically and saved for exact verification
(h12_lift_verify.py).  Variables Z_v >= 0 (16x16 on A,A',B,C), v = (cA0,cA1,xB,xC,cB,cC).  Dual: maximise sum_{xB,xC} Tr Lam_{xB,xC} over
Hermitian multipliers with S_v >= 0, where
  S_v = C_v - Lam_{xB,xC} - (G1 - T1 G1)_{cA0,xB,xC,cB,cC} - (G0 - T0 G0)_{cA1,xB,xC,cB,cC}
        - [xB=0](GB - T2 GB)_{cA0,cA1,xC,cC} - (+DB if xB=1, -DB if xB=0)_{cA0,cA1,xC,cC}
        - [xC=0](GC - T3 GC)_{cA0,cA1,xB,cB} - (+DC if xC=1, -DC if xC=0)_{cA0,cA1,xB,cB},
T_q = Pauli twirl of qubit q (q=0:A, 1:A', 2:B, 3:C).  For any Hermitian values and any feasible Z:
  y_A.P = sum Tr Lam + sum_v Tr[S_v Z_v]  >=  sum Tr Lam + 16 * sum_{xB,xC} min_v lambda_min(S_v)."""
import numpy as np, itertools as it, cvxpy as cp, sys, re, time, pickle
sys.path.insert(0,'.')
exec(open('/workspace/pful-graded/code/stochastic/cyclic/embed/h12_lift_common.py').read())
t0=time.time()
V=list(it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)))
H=lambda:cp.Variable((16,16),hermitian=True)
Lam={k:H() for k in it.product((0,1),(0,1))}
G1={k:H() for k in it.product(range(4),(0,1),(0,1),range(4),range(4))}
G0={k:H() for k in it.product(range(4),(0,1),(0,1),range(4),range(4))}
GB={k:H() for k in it.product(range(4),range(4),(0,1),range(4))}; DB={k:H() for k in GB}
GC={k:H() for k in it.product(range(4),range(4),(0,1),range(4))}; DC={k:H() for k in GC}
TW={}
def tw(G,q,key):
    if key not in TW: TW[key]=G-twirl_cp(G,q)
    return TW[key]
cons=[]
for v in V:
    cA0,cA1,xb,xc,cB,cC=v
    S=Cv(*v)-Lam[xb,xc]-tw(G1[cA0,xb,xc,cB,cC],1,('1',cA0,xb,xc,cB,cC))-tw(G0[cA1,xb,xc,cB,cC],0,('0',cA1,xb,xc,cB,cC))
    kb=(cA0,cA1,xc,cC); kc=(cA0,cA1,xb,cB)
    if xb==0: S=S-tw(GB[kb],2,('B',)+kb)+DB[kb]
    else: S=S-DB[kb]
    if xc==0: S=S-tw(GC[kc],3,('C',)+kc)+DC[kc]
    else: S=S-DC[kc]
    cons.append(S>>0)
pr=cp.Problem(cp.Maximize(cp.real(sum(cp.trace(L) for L in Lam.values()))),cons)
print('built',f'{time.time()-t0:.0f}s',flush=True)
pr.solve(solver='SCS',eps=float(sys.argv[1]) if len(sys.argv)>1 else 1e-6,max_iters=200000,verbose=True)
print(f'LIFT-A dual: status {pr.status}, value {pr.value:.7f}, time {time.time()-t0:.0f}s',flush=True)
val=lambda d:{k:v.value for k,v in d.items()}
pickle.dump(dict(Lam=val(Lam),G1=val(G1),G0=val(G0),GB=val(GB),DB=val(DB),GC=val(GC),DC=val(DC)),open('/tmp/r14/lift_dual.pkl','wb'))
