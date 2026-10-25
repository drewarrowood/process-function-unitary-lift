"""Round 16, item 3 (H.23.3): dual of the INTERSECTION of the lift-A and lift-B relaxations of H.21.8/H.22.1.
Primal (h16_lift_AB.py): two families Z^A (on A,A',B,C) and Z^B (on B,B',A,C), each with all constraints of h12_lift.py, linked by
equality of their induced NS families F^A_{x,c} = F^B_{x,c} (8x8 on A,B,C, all 8 settings x, 64 outcome triples c), where
F^L_{x,c} = (1/2) Tr_{L-copy not used}( sum over the unused copy's outcome of Z^L ), mapped to the (A,B,C) qubit order.
Objective y_A.P computed from family A.  Dual: Hermitian Lam_{x,c} (8x8) for the linking constraint, plus each family's own
multipliers as in h12_lift_dual.py; the cost of family A becomes C_v + K^A_v(Lam), that of family B becomes -K^B_v(Lam), with
K^L_v(Lam) = sum_{xL} emb(Lam'_{x,c}, copy xL)/2 (Lam' = Lam in family-L qubit order).  For any feasible pair (Z^A, Z^B):
  y_A.P = sum_v Tr[C^A_v Z^A_v] + sum_x,c Tr[Lam (F^A - F^B)]
        = sum_L ( sum Tr Lam^L + sum_v Tr[S^L_v Z^L_v] ) >= sum_L ( sum Tr Lam^L + 16 sum_{xM,xN} min_v lambda_min(S^L_v) ).
[NUMERICAL here; exact verification in h16_liftAB_verify.py]"""
import numpy as np, itertools as it, cvxpy as cp, sys, os, time, pickle
SRC=open('h12_lift_common.py').read()
t0=time.time(); eps=float(sys.argv[1]) if len(sys.argv)>1 else 1e-6
FAM=[0,1]+([2] if 'C' in sys.argv else [])
B3=list(it.product((0,1),repeat=3))
Lk=list(it.product(range(8),range(64)))       # (x index, c triple index over 4^3) in ORIGINAL order
Lam={k:cp.Variable((8,8),hermitian=True) for k in Lk}
I2=np.eye(2)
def embm(first):   # constant permutation Q with emb(X,first) = Q (X kron I2) Q^T, X on (L,M,N), extra copy last
    Q=np.zeros((16,16))
    for a in range(8):
        for g in (0,1):
            t=B3[a]; src=a*2+g
            dst=(t[0],g,t[1],t[2]) if first==0 else (g,t[0],t[1],t[2])
            Q[int(''.join(map(str,dst)),2),src]=1
    return Q
Q0,Q1=embm(0),embm(1)
cons=[]; obj=0; FAMVARS={}
for L in FAM:
    os.environ['LIFTP']=str(L); ns={}; exec(SRC,ns)
    perm=[L]+[j for j in range(3) if j!=L]
    orig=lambda t:tuple(t[perm.index(j)] for j in range(3))   # family triple -> original triple
    qidx=np.array([B3.index(orig(B3[a])) for a in range(8)])    # Lam'[a,b] = Lam[qidx[a],qidx[b]]
    H=lambda:cp.Variable((16,16),hermitian=True)
    LamF={k:H() for k in it.product((0,1),(0,1))}
    G1={k:H() for k in it.product(range(4),(0,1),(0,1),range(4),range(4))}
    G0={k:H() for k in it.product(range(4),(0,1),(0,1),range(4),range(4))}
    GB={k:H() for k in it.product(range(4),range(4),(0,1),range(4))}; DB={k:H() for k in GB}
    GC={k:H() for k in it.product(range(4),range(4),(0,1),range(4))}; DC={k:H() for k in GC}
    TW={}
    def tw(G,q,key):
        if key not in TW: TW[key]=G-ns['twirl_cp'](G,q)
        return TW[key]
    def K(v):
        c0,c1,xm,xn,cm,cn=v; out=0
        for xl,cl,Q in ((0,c0,Q0),(1,c1,Q1)):
            xo=orig((xl,xm,xn)); co=orig((cl,cm,cn))
            Lm=Lam[B3.index(xo),16*co[0]+4*co[1]+co[2]][qidx][:,qidx]
            out=out+Q@cp.kron(Lm,I2)@Q.T/2
        return out
    for v in it.product(range(4),range(4),(0,1),(0,1),range(4),range(4)):
        cA0,cA1,xb,xc,cB,cC=v
        S=(ns['Cv'](*v)+K(v)) if L==0 else -K(v)
        S=S-LamF[xb,xc]-tw(G1[cA0,xb,xc,cB,cC],1,('1',cA0,xb,xc,cB,cC))-tw(G0[cA1,xb,xc,cB,cC],0,('0',cA1,xb,xc,cB,cC))
        kb=(cA0,cA1,xc,cC); kc=(cA0,cA1,xb,cB)
        if xb==0: S=S-tw(GB[kb],2,('B',)+kb)+DB[kb]
        else: S=S-DB[kb]
        if xc==0: S=S-tw(GC[kc],3,('C',)+kc)+DC[kc]
        else: S=S-DC[kc]
        cons.append(S>>0)
    obj=obj+cp.real(sum(cp.trace(X) for X in LamF.values()))
    FAMVARS[L]=dict(Lam=LamF,G1=G1,G0=G0,GB=GB,DB=DB,GC=GC,DC=DC)
    print('family',L,'built',f'{time.time()-t0:.0f}s',flush=True)
pr=cp.Problem(cp.Maximize(obj),cons)
pr.solve(solver='SCS',eps=eps,max_iters=200000,verbose=True)
tag=''.join('ABC'[l] for l in FAM)
print(f'LIFT-{tag} intersection dual: status {pr.status}, value {pr.value:.7f}, time {time.time()-t0:.0f}s',flush=True)
val=lambda d:{k:v.value for k,v in d.items()}
pickle.dump(dict(link=val(Lam),fam={L:{n:val(d) for n,d in F.items()} for L,F in FAMVARS.items()}),open(f'/tmp/r16/liftAB_dual_{tag}.pkl','wb'))
