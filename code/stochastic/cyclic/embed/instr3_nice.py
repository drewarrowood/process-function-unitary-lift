"""H.15.7e(B): do 'nice' measurement directions already make H.12 violate a causal inequality?
Instrument for agent k, setting x: projective measurement along Bloch direction n in a finite set D, outcome a, emitted output
o = g(a) with g in {0, 1, a, 1-a} (this contains 'emit the setting').  Objective: min over the 2,432-member pool of valid causal
inequalities (instr_search2) of y.P.  (1) exhaustive over D = octahedral (6 directions) with o = x;  (2) seeded coordinate
descent (exact per-coordinate minimisation over D x modes) for D = octahedral, cube-26 (faces, edges, vertices), icosahedral (12),
icosahedral + dodecahedral (32), and the continuous optimum (each coordinate set to -gradient, which is exact because y.P is
affine in each Bloch vector)."""
import sys, numpy as np, itertools as it, json, time
sys.argv_s=sys.argv; sys.argv=[sys.argv[0]]
import instr_search2 as S, instr_search as IS
sys.argv=sys.argv_s
B3=IS.B3; Hd=IS.Hd
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/np.sqrt(2); ph[4]=np.exp(-1j*np.pi/4)/np.sqrt(2)
psis=np.array([U12[o]@ph for o in range(8)]); Q=psis.reshape(2,2,2,2,2,2)
def pool():
    m=json.load(open('../switchboard/h13/min_cex.json'))['m']
    U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
    psiA=np.array([1,1,1,0,0,-1,0,0])/2; psiB=np.array([1,1,1,0,0,0,0,0])/np.sqrt(3); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
    Y=[]
    for p in ([[abs((U13[o]@psiA)[i])**2 for i in range(8)] for o in range(8)],[[abs((U13[o]@psiB)[i])**2 for i in range(8)] for o in range(8)],[[float(B3[i]==lug(*B3[o])) for i in range(8)] for o in range(8)]):
        Y+=S.images(S.farkas(np.array(p)))
    return np.unique(np.round(np.array(Y),9),axis=0)
Y=pool()
sig=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
def proj(n): return (np.eye(2)+sum(c*s for c,s in zip(n,sig)))/2
def Ek(n,g):   # [a,o,i,j]
    E=np.zeros((2,2,2,2),complex); P0=proj(n)
    for a,Pa in ((0,P0),(1,np.eye(2)-P0)):
        o=[0,1,a,1-a][g]; E[a,o]=Pa
    return E
def corr(Es):
    P=np.zeros((8,8))
    for xi,x in enumerate(B3):
        P[xi]=np.einsum('aqij,brkl,csmn,qrsikm,qrsjln->abc',Es[0][x[0]],Es[1][x[1]],Es[2][x[2]],Q.conj(),Q).real.ravel()
    return P
def val(cfg):   # cfg[k][x]=(n,g)
    P=corr([[Ek(*cfg[k][x]) for x in (0,1)] for k in range(3)]); v=Y@P.ravel(); return v.min(), int(v.argmin())
phi=(1+5**.5)/2; nz=lambda v:tuple(np.array(v)/np.linalg.norm(v))
OCT=[tuple(s*np.eye(3)[i]) for i in range(3) for s in (1,-1)]
EDGE=[nz(v) for v in set(it.permutations((1,1,0)))|set(it.permutations((1,-1,0)))|set(it.permutations((-1,-1,0)))]
VERT=[nz(v) for v in it.product((1,-1),repeat=3)]
cyc=lambda v:[v,(v[1],v[2],v[0]),(v[2],v[0],v[1])]
ICO=[nz(w) for s1 in (1,-1) for s2 in (1,-1) for w in cyc((0,s1,s2*phi))]
DOD=VERT+[nz(w) for s1 in (1,-1) for s2 in (1,-1) for w in cyc((0,s1/phi,s2*phi))]
SETS={'octahedral(6)':OCT,'cube26':OCT+EDGE+VERT,'icosahedral(12)':ICO,'ico+dodeca(32)':ICO+DOD}
if __name__=='__main__':
    t0=time.time(); best=(9,None)
    for c in it.product(range(6),repeat=6):
        cfg=[[(OCT[c[2*k+x]],x) for x in (0,1)] for k in range(3)]
        v,i=val(cfg)
        if v<best[0]: best=(v,c)
    print(f'exhaustive octahedral, o = setting: min_y y.P = {best[0]:+.6f} at {best[1]} ({time.time()-t0:.0f}s)',flush=True)
    for name,D in list(SETS.items())+[('continuous',None)]:
        bb=(9,None)
        for seed in range(int(sys.argv[1]) if len(sys.argv)>1 else 20):
            rng=np.random.default_rng(seed)
            Dset=D if D else OCT
            cfg=[[(Dset[rng.integers(len(Dset))],int(rng.integers(4))) for x in (0,1)] for k in range(3)]
            v,_=val(cfg)
            for sweep in range(12):
                imp=False
                for k in range(3):
                    for x in (0,1):
                        old=cfg[k][x]; cands=[]
                        for g in range(4):
                            if D:
                                for n in D: cands.append((n,g))
                            else:   # exact continuous step for the currently worst y: y.P affine in n
                                _,i=val(cfg); yy=Y[i]
                                f=lambda n:(yy@corr([[Ek(*((n,g) if (kk,xx)==(k,x) else cfg[kk][xx])) for xx in (0,1)] for kk in range(3)]).ravel())
                                f0=f((0,0,0)); gr=np.array([f(tuple(np.eye(3)[j]))-f0 for j in range(3)])
                                cands.append((tuple(-gr/np.linalg.norm(gr)) if np.linalg.norm(gr)>1e-12 else old[0],g))
                        for cnd in cands:
                            cfg[k][x]=cnd; vv,_=val(cfg)
                            if vv<v-1e-12: v=vv; old=cnd; imp=True
                        cfg[k][x]=old
                if not imp: break
            if v<bb[0]: bb=(v,[[(tuple(np.round(n,6)),g) for n,g in r] for r in cfg],seed)
        print(f'{name}: best min_y y.P = {bb[0]:+.6f} (seed {bb[2]}) config {bb[1]}',flush=True)
