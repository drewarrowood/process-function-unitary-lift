"""Round 15, item 3 (H.22.3): classical fine-grained models with bounded reuse.
Claim: every valid tripartite classical process with binary inputs/outputs is reproduced exactly by an acyclic classical
network in which ONE agent (here C, any agent works) is run twice (on inputs 0 and 1) and the other two agents run once each,
in an order chosen classically (dynamic order).  Ingredient: for each deterministic h_C the bipartite slice
W_h(iA,iB|oA,oB) = sum_{iC} p(iA,iB,iC|oA,oB,h(iC)) is a valid bipartite classical process, hence causally separable
(Oreshkov-Costa-Brukner 2012, arXiv:1105.4464, App. 'Causal order in the classical limit').
This script: (1) finds a causally separable decomposition of every slice by LP; (2) builds the network and compares its
exact joint statistics with sum_o p(i|o) prod_k T_k for random classical instruments (2 settings, 2 outcomes).  [NUMERICAL]"""
import itertools as it, numpy as np, sys
from scipy.optimize import linprog
B3=list(it.product((0,1),repeat=3))
h=np.array([[1,1],[1,-1]])/np.sqrt(2); Xp=np.array([[0,1],[1,0]]); I2=np.eye(2)
k3=lambda a,b,c:np.kron(np.kron(a,b),c); mp=np.linalg.matrix_power
H3=k3(h,h,h); Xc=k3(I2,I2,Xp); XA=k3(Xp,I2,I2)
Pre=np.diag([1j**(3*z[2]+2*z[0]+z[1]*z[2]+3*z[0]*z[2]+z[0]*z[1]+2*z[0]*z[1]*z[2]) for z in B3])
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
def Gphi(p): e=np.exp(1j*p); return (1+e)/2*I2+(1-e)/2*Xp
def Vphi(p):   # as in h12_family.py (H.21.7)
    G=Gphi(p); LG=np.zeros((64,64),complex)
    for o in range(8):
        a,b,c=lug(*B3[o]); g=k3(mp(Xp,a),mp(G,b),mp(Xp,c))
        for s in range(8):
            for i in range(8): LG[8*i+o,8*o+s]=g[i,s]
    return np.kron(H3@Xc,H3@XA)@LG.T@np.kron(H3,Xc@Pre@H3)
def forms(V):
    W=V.reshape(8,8,8,8); return np.einsum('ifos,ifot->iost',W.conj(),W).reshape(64,8,8)
rng=np.random.default_rng(15)
B2=list(it.product((0,1),repeat=2))
def slice_(p,h):   # p[iA,iB,iC,oA,oB,oC] ; h=(h(0),h(1))
    return sum(p[:,:,ic,:,:,h[ic]] for ic in (0,1))     # W[iA,iB,oA,oB]
def cs_decomp(W):
    # variables W1[iA,iB,oA,oB] (A before B: iA indep of oA,oB; (iA,iB) indep of oB), W2 (B before A), W1+W2=W, >=0
    n=16; idx=lambda a,b,x,y:((a*2+b)*2+x)*2+y
    Aeq=[];beq=[]
    for a,b,x,y in it.product((0,1),repeat=4):
        r=np.zeros(2*n); r[idx(a,b,x,y)]=1; r[n+idx(a,b,x,y)]=1; Aeq.append(r); beq.append(W[a,b,x,y])
    for a,b,x in it.product((0,1),repeat=3):          # W1 independent of oB
        r=np.zeros(2*n); r[idx(a,b,x,0)]=1; r[idx(a,b,x,1)]=-1; Aeq.append(r); beq.append(0)
    for a,x,y in it.product((0,1),repeat=3):          # sum_b W1 independent of oA
        r=np.zeros(2*n)
        for b in (0,1): r[idx(a,b,x,y)]+=1; r[idx(a,b,1-x,y)]-=1
        if x==0: Aeq.append(r); beq.append(0)
    for a,b,y in it.product((0,1),repeat=3):          # W2 independent of oA
        r=np.zeros(2*n); r[n+idx(a,b,0,y)]=1; r[n+idx(a,b,1,y)]=-1; Aeq.append(r); beq.append(0)
    for b,x,y in it.product((0,1),repeat=3):          # sum_a W2 independent of oB
        r=np.zeros(2*n)
        for a in (0,1): r[n+idx(a,b,x,y)]+=1; r[n+idx(a,b,x,1-y)]-=1
        if y==0: Aeq.append(r); beq.append(0)
    res=linprog(np.zeros(2*n),A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=(0,None),method='highs')
    assert res.status==0, 'not causally separable?!'
    z=res.x; return z[:n].reshape(2,2,2,2), z[n:].reshape(2,2,2,2)
def rand_inst():    # T[x][a,o,i] classical instrument: P(a,o|i,x)
    T=rng.random((2,2,2,2)); return T/T.sum((1,2),keepdims=True)   # [x,a,o,i]
def network(p,TA,TB,TC):
    """exact joint P[iA,iB,iC,aA,aB,aC,oA,oB,oC] produced by the network (C run twice, A,B once each, dynamic order)"""
    out=np.zeros((2,)*9)
    dec={h:cs_decomp(slice_(p,h)) for h in it.product((0,1),repeat=2)}
    for a0,o0,a1,o1 in it.product((0,1),repeat=4):
        wC=TC[a0,o0,0]*TC[a1,o1,1]; h=(o0,o1); W=slice_(p,h); W1,W2=dec[h]
        for iA,iB,oA,oB,aA,aB in it.product((0,1),repeat=6):
            # branch A first: P(iA) P(aA,oA|iA) P(iB|iA,oA) P(aB,oB|iB); W1 = P(iA)P(iB|iA,oA) unnormalised
            # branch B first similarly; both branches give W_k(iA,iB|oA,oB)*TA*TB
            pAB=(W1[iA,iB,oA,oB]+W2[iA,iB,oA,oB])*TA[aA,oA,iA]*TB[aB,oB,iB]
            if pAB==0: continue
            for iC in (0,1):
                cond=p[iA,iB,iC,oA,oB,h[iC]]/W[iA,iB,oA,oB]      # N samples iC given everything
                aC,oC=(a0,o0) if iC==0 else (a1,o1)
                out[iA,iB,iC,aA,aB,aC,oA,oB,oC]+=wC*pAB*cond
    return out
def target(p,TA,TB,TC):
    return np.einsum('ijkxyz,axi,byj,czk->ijkabcxyz',p,TA,TB,TC)
def lugano():
    p=np.zeros((2,)*6)
    for o in it.product((0,1),repeat=3):
        a,b,c=o; p[((1-b)*c,(1-c)*a,(1-a)*b)+o]=1
    return p
def from_V(V,psi):
    P=forms(V); pr=np.real(np.einsum('s,rst,t->r',psi.conj(),P,psi)).reshape(8,8)  # [i,o]
    return pr.reshape((2,)*6)
procs={'Lugano PF':lugano()}
for name,phi in (('H.13.2 (V_pi)',np.pi),('H.12 (V_pi/2)',np.pi/2)):
    for t in range(3):
        psi=rng.normal(size=8)+1j*rng.normal(size=8); psi/=np.linalg.norm(psi); procs[f'{name} src{t}']=from_V(Vphi(phi),psi)
    psi=np.zeros(8); psi[0]=1; procs[f'{name} |000>']=from_V(Vphi(phi),psi)
worst=0
for name,p in procs.items():
    assert np.allclose(p.sum((0,1,2)),1)
    # validity on all 64 deterministic interventions
    for hs in it.product(range(4),repeat=3):
        f=[((h>>0)&1,(h>>1)&1) for h in hs]
        tot=sum(p[i+tuple(f[k][i[k]] for k in range(3))] for i in it.product((0,1),repeat=3)); assert abs(tot-1)<1e-12
    dev=0
    for trial in range(20):
        x=rng.integers(0,2,3); T=[rand_inst()[x[k]] for k in range(3)]
        dev=max(dev,abs(network(p,*T)-target(p,*T)).max())
    worst=max(worst,dev); print(f'{name:22s}: all 4 slices causally separable (LP); network vs process, 20 random instrument triples: max dev {dev:.1e}',flush=True)
print(f'ALL OK, worst deviation {worst:.1e}')
