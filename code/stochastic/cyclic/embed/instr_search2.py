"""H.15.7d(B''): general-instrument search for causal-inequality violations by H.12 (and Z8), with a facet-targeted optimiser.
Agent k, setting x_k: a general 4-outcome qubit POVM {E^{k,x}_{a,o}} on its input; outcome a_k, emitted classical output o_k
(the board decoheres o, so this is the most general local instrument with classical output and no memory).  Covers 3-outcome
POVMs and rank-1 projective measurements in arbitrary bases as special cases.  P(a|x) = sum_o <psi_o| (x)_k E^{k,x_k}_{a_k,o_k} |psi_o>.
Objective (avoids the t=1 plateau of the robustness LP): soft-min of y.P over a pool Y of valid causal inequalities
(min over the 138,304 deterministic causal strategies = 0): the exact Farkas certificates of H.15.7b (H.13.2 phi_A, phi_B, Lugano)
and all their images under party permutations, setting flips and setting-dependent outcome flips (3 x 3072).  L-BFGS-B with
random restarts (seeded); the best point is re-checked with the robustness LP of instr_search.py.  y.P < 0 = violation."""
import itertools as it, numpy as np, sys, json, time
from fractions import Fraction as Fr
from scipy.optimize import linprog, minimize
sys.argv_saved=sys.argv; sys.argv=[sys.argv[0]]
import instr_search as IS
sys.argv=sys.argv_saved
B3=IS.B3; V=IS.V; A=IS.A
def farkas(p):
    b=np.ravel(p); r=linprog(b,A_ub=-A.T.toarray() if hasattr(A,'toarray') else -A.T,b_ub=np.zeros(len(V)),bounds=(-1,1),method='highs')
    y=np.array([float(Fr(v).limit_denominator(64)) for v in r.x]); return y
def images(y):
    Y=y.reshape(8,8); out=set()
    for pi in it.permutations(range(3)):
        for sx in it.product((0,1),repeat=3):
            for fa in it.product((0,1),repeat=6):     # a_k -> a_k xor fa[2k+x_k]
                Z=np.zeros((8,8))
                for xi,x in enumerate(B3):
                    for ai,a in enumerate(B3):
                        x2=[0]*3; a2=[0]*3
                        for k in range(3): x2[pi[k]]=x[k]^sx[k]; a2[pi[k]]=a[k]^fa[2*k+x[k]]
                        Z[B3.index(tuple(x2)),B3.index(tuple(a2))]=Y[xi,ai]
                out.add(tuple(np.round(Z.ravel(),9)))
    return [np.array(z) for z in out]
def povm(theta):   # theta: 32 reals -> 4 PSD 2x2 summing to I
    M=(theta[:16]+1j*theta[16:]).reshape(4,2,2); E=np.einsum('jki,jkl->jil',M.conj(),M); S=E.sum(0)
    w,v=np.linalg.eigh(S); Si=v@np.diag(w**-.5)@v.conj().T; return np.einsum('ij,ajk,kl->ail',Si,E,Si)
def corr(psis,theta):
    E=[[povm(theta[32*(2*k+x):32*(2*k+x+1)]).reshape(2,2,2,2) for x in (0,1)] for k in range(3)]   # [a,o,i,j]
    Q=psis.reshape(2,2,2,2,2,2); P=np.zeros((8,8))
    for xi,x in enumerate(B3):
        T=np.einsum('aqij,brkl,csmn,qrsikm,qrsjln->abc',E[0][x[0]],E[1][x[1]],E[2][x[2]],Q.conj(),Q)
        P[xi]=T.real.ravel()
    return P
def init(rng,r):
    # even restarts: 'measure in a random basis, emit o = setting' (the H.15.7b operation, rotated) plus noise;
    # odd restarts: 'measure in a random basis, emit o = g(outcome)' with g random; noise keeps every POVM element full rank
    th=np.zeros(192)
    for k in range(3):
        for x in (0,1):
            q,_=np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))); g=rng.integers(4)
            M=0.05*(rng.normal(size=(4,2,2))+1j*rng.normal(size=(4,2,2)))
            for a in (0,1):
                o=x if r%2==0 else [0,1,a,1-a][g]
                M[2*a+o]+=np.outer(np.eye(2)[a],q[:,a].conj())
            j=2*k+x; th[32*j:32*j+16]=M.real.ravel(); th[32*j+16:32*j+32]=M.imag.ravel()
    return th
def run(name,psis,seeds,Y,restarts,beta=40.):
    Ym=np.array(Y); best=(9,None)
    f=lambda th:(lambda v:-np.log(np.exp(-beta*(v-v.min())).sum())/beta+v.min())(Ym@corr(psis,th).ravel())
    for sd in seeds:
        rng=np.random.default_rng(sd)
        for r in range(restarts):
            th=init(rng,r); res=minimize(f,th,method='L-BFGS-B',options=dict(maxiter=300))
            P=corr(psis,res.x); v=(Ym@P.ravel()).min()
            if v<best[0]: best=(v,res.x,sd,r)
            print(f'  {name} seed {sd} restart {r}: min_y y.P = {v:+.6f}',flush=True)
    v,th,sd,r=best; P=corr(psis,th); t=IS.robust(P)
    print(f'{name}: BEST min_y y.P = {v:+.6f} (seed {sd}, restart {r}); robustness LP t = {t:.6f} -> {"VIOLATION" if v<-1e-7 else "no violation found"}',flush=True)
    return best
if __name__=='__main__':
    import json
    m=json.load(open('../switchboard/h13/min_cex.json'))['m']; Hd=IS.Hd
    U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
    psiA=np.array([1,1,1,0,0,-1,0,0])/2; psiB=np.array([1,1,1,0,0,0,0,0])/np.sqrt(3)
    pA=np.array([[abs((U13[o]@psiA)[i])**2 for i in range(8)] for o in range(8)])
    pB=np.array([[abs((U13[o]@psiB)[i])**2 for i in range(8)] for o in range(8)])
    lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
    pL=np.array([[float(B3[i]==lug(*B3[o])) for i in range(8)] for o in range(8)])
    Y=[]
    for p in (pA,pB,pL):
        y=farkas(p); assert min(y[8*np.arange(8)+v].sum() for v in V[:2000])>=-1e-9
        Y+=images(y)
    Y=np.unique(np.round(np.array(Y),9),axis=0)
    # images of a valid inequality under these relabelings (symmetries of the causal polytope) are valid; spot-check 64 of them
    VA=A.toarray(); chk=Y[np.random.default_rng(0).choice(len(Y),64,replace=False)]
    print('pool size',len(Y),'; spot-check min over all causal strategies of 64 random members:',float((chk@VA).min()),flush=True)
    which=sys.argv[1]; seeds=[int(s) for s in sys.argv[2].split(',')]; R=int(sys.argv[3])
    MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
    U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
    ph=np.zeros(8,complex); ph[3]=1/np.sqrt(2); ph[4]=np.exp(-1j*np.pi/4)/np.sqrt(2)
    if which=='h13': run('H.13.2 phi_A (control)',np.array([U13[o]@psiA for o in range(8)]),seeds,Y,R)
    if which=='h12': run('H.12 switchboard',np.array([U12[o]@ph for o in range(8)]),seeds,Y,R)
    if which=='z8':
        mz=[[0,0,0,0,0,0,0,0],[0,0,1,1,1,1,1,1],[0,0,0,0,1,0,1,0],[0,0,1,1,2,1,2,1],[0,0,0,1,0,0,0,1],[0,0,1,2,1,1,1,2],[0,0,0,1,1,0,1,1],[0,0,1,2,2,1,2,2]]
        U=np.array([Hd@np.diag([np.exp(2j*np.pi*mz[o][z]/8) for z in range(8)])@Hd for o in range(8)])
        v=np.load('z8_source.npy'); run('Z8 class 10515',np.array([U[o]@v for o in range(8)]),seeds,Y,R)
