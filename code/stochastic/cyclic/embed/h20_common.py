"""Round 20 common data: PF list, facets of the 10 open orbits (representatives as in H.23.1a/H.25.4), refined PFs."""
import itertools as it, numpy as np, gzip
F='../../physics/facets/'
B3=list(it.product((0,1),repeat=3))           # index = 4*b0+2*b1+b2, party 0 = most significant bit
PF=np.load('../pfs744.npy').astype(int)        # PF[n][i][o]
Zc=np.load(F+'Z.npy').astype(np.int64)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hi=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],np.int64)
valsI=Zc@Hi[:,:37].T+Hi[:,37]
vals=valsI.astype(float); A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
canon=np.load('../switchboard/h13/xviol.npz')['canon'].astype(int)
OPEN=[26,28,30,31,54,57,66,69,75,81]
REP={orb:int(np.where(canon==orb)[0][0]) for orb in OPEN}
PFSET={tuple(int(np.argmax(PF[n][:,o])) for o in range(8)) for n in range(744)}   # PF as tuple o -> i (index)
def others(k,o):  # o_{-k} as an index 0..3 (bits of the other two parties in order)
    b=B3[o]; r=[b[j] for j in range(3) if j!=k]; return 2*r[0]+r[1]
def setpartitions(n=4):
    out=[]
    def rec(i,lab,m):
        if i==n: out.append(tuple(lab)); return
        for c in range(m+1): rec(i+1,lab+[c],max(m,c+1))
    rec(0,[],0); return out
PARTS=setpartitions()   # 15 restricted-growth strings over the 4 values of o_{-k}
def is_refined_pf(parts):
    """parts[k][j] = block of o_{-k}=j.  Valid iff every 2-colouring of every party's blocks gives a binary PF."""
    nb=[max(p)+1 for p in parts]
    for cols in it.product(*[list(it.product((0,1),repeat=n)) for n in nb]):
        f=tuple(4*cols[0][parts[0][others(0,o)]]+2*cols[1][parts[1][others(1,o)]]+cols[2][parts[2][others(2,o)]] for o in range(8))
        if f not in PFSET: return False
    return True
