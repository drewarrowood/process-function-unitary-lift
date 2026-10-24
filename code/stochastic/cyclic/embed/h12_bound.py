"""H.15.9(C): how far can H.12 violate the causal inequality y?  Labels in the printout.
P(a|x) = sum_o psi_o^dag (E^A_{a_A o_A|x_A} (x) E^B (x) E^C) psi_o, psi_o = U_o ph (H.15.7d: general qubit instruments on this board reduce
exactly to 4-outcome POVMs {E_{a,o|x}}, because the board decoheres AO into F).
 lower side: seesaw (each step an exact SDP over one party's instrument, others fixed)  -> achievable values  [NUMERICAL]
 upper side: relaxation.  Replace the product E^A(x)E^B(x)E^C by one operator Z_{ao|x} >= 0 on AI (8x8) per joint setting x with
   sum_{ao} Z_{ao|x} = 1,  sum over party k's (a_k,o_k) = 1_k (x) R (R independent of x_k)  [true for products],
   and (option) Z^{T_k} >= 0 for each party k (PPT; true for products).  min y.P over this set <= min over real instruments.
   SDP solver output is floating point; the certified bound is the dual value, checked in the log  [NUMERICAL, dual-certified to solver tol]."""
import numpy as np, itertools as it, cvxpy as cp, sys, re, time
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2
psi=np.array([U[o]@ph for o in range(8)])            # psi[o] on AI (z_A z_B z_C)
Ys={}
for fn,tag in (('instr2_exact.log','y_A (H.15.7d, -0.7057)'),('instr3_exact.log','y_B (cube-26, -0.2224)')):
    Ys[tag]=np.array(eval(re.search(r'\[.*?\]',open(fn).readline()).group()),float).reshape(8,8)   # y[x,a]
def corr(E):   # E[k][x][a][o] 2x2
    P=np.zeros((8,8))
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            P[xi,ai]=sum(np.real(psi[o].conj()@np.kron(np.kron(E[0][x[0]][a[0]][B3[o][0]],E[1][x[1]][a[1]][B3[o][1]]),E[2][x[2]][a[2]][B3[o][2]])@psi[o]) for o in range(8))
    return P
def Gk(E,y,k):   # objective = sum_{x_k,a_k,o_k} Tr[E^k G]
    G=np.zeros((2,2,2,2,2),complex)
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            if y[xi,ai]==0: continue
            for o in range(8):
                ob=B3[o]; ops=[E[j][x[j]][a[j]][ob[j]] if j!=k else np.eye(2) for j in range(3)]
                M=np.kron(np.kron(ops[0],ops[1]),ops[2])
                T6=(M@np.outer(psi[o],psi[o].conj())).reshape(2,2,2,2,2,2)
                idx={0:'aBCdBC',1:'AbCAeC',2:'ABcABf'}[k]
                red=np.einsum(idx+'->'+{0:'ad',1:'be',2:'cf'}[k],T6)
                G[x[k],a[k],ob[k]]+=y[xi,ai]*red   # Tr[(E(x)M)rho] = Tr[E red]
    return G
def best_party(G):
    E=[[None,None] for _ in range(2)]; val=0
    for x in (0,1):
        V=[cp.Variable((2,2),hermitian=True) for _ in range(4)]
        obj=sum(cp.real(cp.trace(V[2*a+o]@G[x,a,o])) for a in (0,1) for o in (0,1))
        pr=cp.Problem(cp.Minimize(obj),[v>>0 for v in V]+[sum(V)==np.eye(2)]); pr.solve(solver='CLARABEL')
        E[x]=[[V[2*a+o].value for o in (0,1)] for a in (0,1)]; val+=pr.value
    return E,val
def rand_inst():
    E=[]
    for x in (0,1):
        Ms=[ (lambda A:A@A.conj().T)(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))) for _ in range(4)]
        S=sum(Ms); w,v=np.linalg.eigh(S); Si=v@np.diag(w**-.5)@v.conj().T
        Ms=[Si@M@Si for M in Ms]; E.append([[Ms[0],Ms[1]],[Ms[2],Ms[3]]])
    return E
mode=sys.argv[2] if len(sys.argv)>2 else 'both'
if mode in ('seesaw','both'):
    for tag,y in Ys.items():
        best=9
        for rs in range(int(sys.argv[3]) if len(sys.argv)>3 else 6):
            E=[rand_inst() for _ in range(3)]; prev=9
            for sweep in range(60):
                for k in range(3):
                    E[k],v=best_party(Gk(E,y,k))
                if prev-v<1e-9: break
                prev=v
            P=corr(E); val=(y*P).sum(); assert abs(val-v)<1e-5,(val,v); best=min(best,val)
            print(f'seesaw {tag} restart {rs}: y.P = {val:.6f} (check rows {np.abs(P.sum(1)-1).max():.1e}) sweeps {sweep}',flush=True)
        print(f'SEESAW BEST {tag}: {best:.6f}',flush=True)
if mode in ('relax','both'):
    for ppt in ((False,) if "noppt" in sys.argv else (True,) if "ppt" in sys.argv else (False,True)):
        for tag,y in Ys.items():
            t=time.time(); Z={}
            for xi in range(8):
                for c in range(64): Z[xi,c]=cp.Variable((8,8),hermitian=True)
            # outcome c = (aA,oA,aB,oB,aC,oC) bits, a party's pair = 2 bits
            pc=lambda c,k:(c>>(2*(2-k)))&3
            cons=[]
            for xi in range(8):
                cons+=[Z[xi,c]>>0 for c in range(64)]; cons.append(sum(Z[xi,c] for c in range(64))==np.eye(8))
            for k in range(3):
                for xi,x in enumerate(B3):
                    for rest in range(16):   # other two parties' (a,o) pairs
                        cs=[c for c in range(64) if sum(pc(c,j)<<(2*(1-[jj for jj in range(3) if jj!=k].index(j))) for j in range(3) if j!=k)==rest]
                        S=sum(Z[xi,c] for c in cs)
                        Ps=[np.eye(2),np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
                        emb=lambda Pm:np.kron(np.kron(Pm if k==0 else np.eye(2),Pm if k==1 else np.eye(2)),Pm if k==2 else np.eye(2))
                        cons.append(S==sum(emb(Pm)@S@emb(Pm).conj().T for Pm in Ps)/4)
                        # independence of x_k
                        if x[k]==1:
                            x0=list(x); x0[k]=0; S0=sum(Z[B3.index(tuple(x0)),c] for c in cs); cons.append(S==S0)
                if ppt:
                    for xi in range(8):
                        for c in range(64): cons.append(cp.partial_transpose(Z[xi,c],[2,2,2],k)>>0)
            obj=0
            for xi in range(8):
                for c in range(64):
                    a=tuple((pc(c,k)>>1) for k in range(3)); o=tuple(pc(c,k)&1 for k in range(3))
                    w=y[xi,B3.index(a)]
                    if w: obj=obj+w*cp.real(cp.trace(Z[xi,c]@np.outer(psi[B3.index(o)],psi[B3.index(o)].conj())))
            pr=cp.Problem(cp.Minimize(obj),cons); pr.solve(solver='SCS',eps=1e-6,max_iters=100000)
            print(f'RELAX {"NS+PPT" if ppt else "NS"} {tag}: status {pr.status}, primal {pr.value:.6f}, time {time.time()-t:.0f}s',flush=True)
if mode=='warm':   # seesaw started from the saved H.15.7d optimum (instr2_h12_best.npy, value -0.7057 for y_A)
    th=np.load('instr2_h12_best.npy'); y=Ys['y_A (H.15.7d, -0.7057)']
    def povm(t):
        M=(t[:16]+1j*t[16:]).reshape(4,2,2); E=np.einsum('jki,jkl->jil',M.conj(),M); S=E.sum(0)
        w,v=np.linalg.eigh(S); Si=v@np.diag(w**-.5)@v.conj().T; return np.einsum('ij,ajk,kl->ail',Si,E,Si)
    E=[[ (lambda q:[[q[0],q[1]],[q[2],q[3]]])(povm(th[32*(2*k+x):32*(2*k+x+1)])) for x in (0,1)] for k in range(3)]
    print('warm start y_A.P =',(y*corr(E)).sum())
    prev=9
    for sweep in range(200):
        for k in range(3): E[k],v=best_party(Gk(E,y,k))
        if prev-v<1e-10: break
        prev=v
    print(f'warm seesaw y_A: {(y*corr(E)).sum():.6f} after {sweep} sweeps',flush=True)
    np.save('h12_bound_warm_E.npy',np.array([[[[E[k][x][a][o] for o in (0,1)] for a in (0,1)] for x in (0,1)] for k in range(3)]))
