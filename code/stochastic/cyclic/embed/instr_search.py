"""H.15.7(B'): search over local instruments for causal-inequality violations by the H.12 switchboard and a Z8 board.
Agent k, setting x_k: measure input qubit in basis n_{k,x} (outcome a_k = b), emit o_k = g_{k,x}(b), g in {0,1,b,1-b}.
P(a|x) = sum_o |<n(a)|U_o psi>|^2 [o = g_x(a)].  Robustness LP over the 138,304 deterministic causal strategies:
max t s.t. t P + (1-t) uniform is causal;  t<1 <=> violation.  Then exact rational Farkas check (rational P only)."""
import itertools as it, numpy as np, sys, json, time
from scipy.optimize import linprog
from scipy.sparse import csc_matrix, hstack
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/np.sqrt(8)
def verts():
    V=set()
    for k1 in range(3):
        oth=[t for t in range(3) if t!=k1]
        for g1 in it.product((0,1),repeat=2):
          for h in it.product(range(2),repeat=2):
            for g2 in it.product((0,1),repeat=4):
              for g3 in it.product((0,1),repeat=8):
                out=[]
                for xi,x in enumerate(B3):
                    a=[0,0,0]; a[k1]=g1[x[k1]]; k2=oth[h[x[k1]]]; k3=oth[1-h[x[k1]]]
                    a[k2]=g2[2*x[k1]+x[k2]]; a[k3]=g3[xi]; out.append(B3.index(tuple(a)))
                V.add(tuple(out))
    return np.array(sorted(V))
V=verts(); nV=len(V)
rows=(8*np.arange(8)[None,:]+V).ravel(); cols=np.repeat(np.arange(nV),8)
A=csc_matrix((np.ones(len(rows)),(rows,cols)),shape=(64,nV))
u=np.full(64,1/8)
def robust(p):
    b=np.ravel(p); col=csc_matrix((b-u)[:,None]*-1)
    r=linprog(np.r_[np.zeros(nV),-1],A_eq=hstack([A,col]).tocsc(),b_eq=u,bounds=[(0,None)]*nV+[(0,10)],method='highs')
    return r.x[-1] if r.status==0 else None
def bloch(th,ph):
    v0=np.array([np.cos(th/2),np.exp(1j*ph)*np.sin(th/2)]); v1=np.array([-np.exp(-1j*ph)*np.sin(th/2),np.cos(th/2)]); return np.array([v0,v1]).conj()
G=[lambda b:0,lambda b:1,lambda b:b,lambda b:1-b]
def corr(psis,ins):   # ins[k][x]=(th,ph,g)
    M={}
    for k in range(3):
        for x in (0,1): M[k,x]=bloch(*ins[k][x][:2])
    P=np.zeros((8,8))
    for xi,x in enumerate(B3):
        for ai,a in enumerate(B3):
            o=tuple(G[ins[k][x[k]][2]](a[k]) for k in range(3)); oi=B3.index(o)
            amp=np.einsum('i,j,k,ijk->',M[0,x[0]][a[0]],M[1,x[1]][a[1]],M[2,x[2]][a[2]],psis[oi].reshape(2,2,2))
            P[xi,ai]=abs(amp)**2
    return P
DIRS=[(th,ph) for th in (0,np.pi/4,np.pi/2,3*np.pi/4) for ph in (0,np.pi/4,np.pi/2,3*np.pi/4)]+[(0,0)]
def search(name,psis,N,seed=0):
    rng=np.random.default_rng(seed); best=(9,None); t0=time.time()
    base=[[(0,0,x+0) for x in (0,1)] for k in range(3)]   # x=o, computational: the earlier test
    for cand in [base]+[None]*N:
        if cand is None:
            cand=[[ (*DIRS[rng.integers(len(DIRS))], int(rng.integers(4))) for x in (0,1)] for k in range(3)]
        P=corr(psis,cand); assert np.allclose(P.sum(1),1),P.sum(1)
        t=robust(P)
        if t is not None and t<best[0]: best=(t,cand)
    # hill climb in continuous angles from best
    t,c=best; c=[list(z) for z in c]
    for step in range(N):
        k,x=rng.integers(3),rng.integers(2); old=c[k][x]
        c[k][x]=(old[0]+rng.normal(0,.3),old[1]+rng.normal(0,.3),old[2] if rng.random()<.8 else int(rng.integers(4)))
        tt=robust(corr(psis,c))
        if tt is not None and tt<t: t=tt
        else: c[k][x]=old
    print(f'{name}: best robustness t = {t:.6f} ({"VIOLATION" if t<1-1e-7 else "no violation found"}); {time.time()-t0:.0f}s',flush=True)
    return t,c
if __name__=='__main__':
    MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
    U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
    ph=np.zeros(8,complex); ph[3]=1/np.sqrt(2); ph[4]=np.exp(-1j*np.pi/4)/np.sqrt(2)
    which=sys.argv[1]; N=int(sys.argv[2])
    if which=='h13':
        import json; m=json.load(open('../switchboard/h13/min_cex.json'))['m']
        U=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
        psi=np.array([1,1,1,0,0,-1,0,0])/2; search('H.13.2 phi_A (control)',[U[o]@psi for o in range(8)],N)
    if which=='h12': search('H.12 switchboard',[U12[o]@ph for o in range(8)],N,int(sys.argv[3]) if len(sys.argv)>3 else 0)
    if which=='z8':
        mz=[[0,0,0,0,0,0,0,0],[0,0,1,1,1,1,1,1],[0,0,0,0,1,0,1,0],[0,0,1,1,2,1,2,1],[0,0,0,1,0,0,0,1],[0,0,1,2,1,1,1,2],[0,0,0,1,1,0,1,1],[0,0,1,2,2,1,2,2]]
        U=np.array([Hd@np.diag([np.exp(2j*np.pi*mz[o][z]/8) for z in range(8)])@Hd for o in range(8)])
        v=np.load('z8_source.npy'); search('Z8 class 10515 (H.14.2 source)',[U[o]@v for o in range(8)],N)
