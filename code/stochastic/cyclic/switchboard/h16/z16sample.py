"""H.16 goal 5 [numerical]: random backtracking sampler of pure Z_16 X-type boards (exact integer Pauli test,
same gauge/representation as h13/z8enum.py), scored on the 23 never-crossed facet orbits (all facets in each
orbit, max over source states)."""
import numpy as np, itertools as it, sys, gzip, json
N=16; h=N//2; seed=int(sys.argv[1]); NB=int(sys.argv[2]); rng=np.random.default_rng(seed)
B3=list(it.product((0,1),repeat=3)); H=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3])
Zb=np.zeros((N,h),np.int64)
for k in range(N): Zb[k,k%h]=1 if k<h else -1
def allowed(Dm,delta):
    D=[t for t in range(3) if (Dm>>(2-t))&1]; bad=[ai for ai,a in enumerate(B3) if all(a[t] for t in D)]
    C=np.einsum('az,nzc->nac',H[bad],Zb[delta%N]); return ~(C!=0).any((1,2))
def edgeset(k):
    others=[t for t in range(3) if t!=k]; out=[]
    for vals in it.product(range(N),repeat=3):
        f=dict(zip([(0,1),(1,0),(1,1)],vals)); f[(0,0)]=0
        out.append([f[(z[others[0]],z[others[1]])] for z in B3])
    return np.array(out)
E={k:edgeset(k) for k in range(3)}
order=[0b000,0b100,0b010,0b001,0b110,0b101,0b011,0b111]
def sample():
    b=np.zeros((8,8),np.int64)
    for step,o in enumerate(order[1:],1):
        prev=order[:step]; nb=next(q for q in prev if bin(o^q).count('1')==1); k=[t for t in range(3) if (o^nb)>>(2-t)&1][0]
        cand=(b[nb][None]+E[k])%N; ok=np.ones(len(cand),bool)
        for q in prev:
            if q!=nb: ok&=allowed(o^q,cand-b[q])
        idx=np.nonzero(ok)[0]
        # bias: prefer candidates with odd exponents (genuinely Z16) half the time
        if rng.random()<0.5:
            odd=idx[(cand[idx]%2==1).any(1)]
            if len(odd): idx=odd
        b[o]=cand[rng.choice(idx)]
    return b
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
canon=np.load('../h13/xviol.npz')['canon'].astype(int)
NC=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81,92]
sel=np.nonzero(np.isin(canon,NC))[0]; Hs=Hm[sel]
vals=Zc@Hs[:,:37].T+Hs[:,37]; T=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals,rcond=None)[0].T/vals.max(0)[:,None]
Hd=H/8**.5; zeta=np.exp(2j*np.pi/N)
best={o:-1.0 for o in NC}; arg={}
for n in range(NB):
    b=sample(); U=np.stack([Hd@np.diag(zeta**b[o])@Hd for o in range(8)])
    P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
    v=-np.linalg.eigvalsh(np.einsum('fr,rst->fst',T[:,:64],P)+T[:,64,None,None]*np.eye(8))[:,0]
    for o in NC:
        m=v[canon[sel]==o].max()
        if m>best[o]: best[o]=float(m); arg[o]=b.tolist()
    if n%500==0: print(n,max(best.values()),flush=True)
print('max over NC orbits (positive = violation):',json.dumps(best))
json.dump(dict(best=best,arg=arg),open('z16_%d.json'%seed,'w'))
