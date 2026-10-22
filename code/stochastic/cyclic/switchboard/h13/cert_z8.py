"""H.14.2 EXACT certificates (arithmetic in Q(zeta_8), no floats in the checks) that Z_8 X-type pure switchboards
violate facets in orbits never violated by Z_4 boards.  Floats are used only to choose the facet and a source vector;
the source v is then rounded to Gaussian rationals, and everything below is exact:
(1) U_o unitary, (2) Pauli rule H.8.1 (=> pure, H.8.1-H.8.2), (3) p valid, (4) facet value on p < 0 (sign of a+b sqrt2)."""
import json, itertools as it, gzip, numpy as np, flint, sys
from fractions import Fraction as Fr
exec(open('../c1/exact_cex.py').read().split("B3=list")[0].split('import json, itertools as it\nfrom fractions import Fraction as Fr\n')[1])  # Q8, z, ZERO, ONE, SQ2, HALF
B3=list(it.product((0,1),repeat=3))
R=np.load('xreps_z8.npy').astype(int); V=np.load('xviol_z8.npz')['viol']
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(int); Zc=np.load(F+'Z.npy').astype(int)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))]); vals=Zc@Hm[:,:37].T+Hm[:,37]
canon=np.load('xviol.npz')['canon']
Tf=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals.astype(float),rcond=None)[0].T
inv8=SQ2*Q8([Fr(1,4),0,0,0])
H=[[inv8*(ONE if sum(a*b for a,b in zip(B3[x],B3[y]))%2==0 else Q8([-1,0,0,0])) for y in range(8)] for x in range(8)]
def mm(A,B): return [[sum((A[i][l]*B[l][j] for l in range(8)),ZERO) for j in range(8)] for i in range(8)]
def dag(A): return [[A[j][i].conj() for j in range(8)] for i in range(8)]
I8=[[ONE if i==j else ZERO for j in range(8)] for i in range(8)]
def pauli(a,b):
    M=[[ZERO]*8 for _ in range(8)]
    for e in range(8):
        eb=B3[e]; M[B3.index(tuple(x^y for x,y in zip(eb,a)))][e]=Q8([(-1)**sum(bb*x for bb,x in zip(b,eb)),0,0,0])
    return M
P={(a,b):pauli(a,b) for a in B3 for b in B3}
def sgn(x):
    a,b=x
    if a>=0 and b>=0: return (a>0 or b>0)*1
    if a<=0 and b<=0: return -1*((a<0) or (b<0))
    s=1 if a>0 else -1; return s if a*a>2*b*b else (-s if a*a<2*b*b else 0)
def certify(n,orbits):
    m=R[n]; U=[mm(mm(H,[[z(int(m[o][x])) if x==y else ZERO for y in range(8)] for x in range(8)]),H) for o in range(8)]
    assert all(mm(U[o],dag(U[o]))==I8 for o in range(8))
    bad=0
    for o in range(8):
        for q in range(8):
            if o==q: continue
            Kq=mm(U[o],dag(U[q])); Dl=[t for t in range(3) if B3[o][t]!=B3[q][t]]
            for (a,b),S in P.items():
                if all(a[t] or b[t] for t in Dl):
                    bad+= not sum((S[j][i].conj()*Kq[j][i] for i in range(8) for j in range(8)),ZERO).iszero()
    assert bad==0; print('class',n,'phases (zeta_8 powers):',m.tolist(),'\n (1) unitary, (2) Pauli rule: exact',flush=True)
    zeta=np.exp(2j*np.pi/8); Uf=np.stack([np.array([[complex(sum(float(c)*zeta**t for t,c in enumerate(U[o][i][j].c))) for j in range(8)] for i in range(8)]) for o in range(8)])
    Pf=np.einsum('ois,oit->iost',Uf.conj(),Uf).reshape(64,8,8)
    res={}
    for orb in orbits:
        fs=np.nonzero(canon==orb)[0]; Fm=np.einsum('fr,rst->fst',Tf[fs,:64],Pf)+Tf[fs,64,None,None]*np.eye(8)
        w,vv=np.linalg.eigh(Fm); j=w[:,0].argmin(); f=int(fs[j]); v=vv[j][:,0]
        vq=[Q8([Fr(round(x.real*10**4),10**4),0,Fr(round(x.imag*10**4),10**4),0]) for x in v]   # Gaussian rationals (zeta^2=i)
        M=flint.fmpq_mat(744,66,[int(x) for row in np.c_[PF.reshape(744,-1),np.ones(744,int),vals[:,f]] for x in row])
        RR,rk=M.rref(); g=[Fr(0)]*65
        for r in range(rk):
            piv=next(c for c in range(66) if RR[r,c]!=0); assert piv<65; g[piv]=Fr(int(RR[r,65].p),int(RR[r,65].q))
        nv=sum((x*x.conj() for x in vq),ZERO)       # |v|^2 (rational)
        amp2=[[None]*8 for _ in range(8)]
        for o in range(8):
            for i in range(8):
                a=sum((U[o][i][s]*vq[s] for s in range(8)),ZERO); t=a*a.conj(); assert t.c[2]==0 and t.c[1]==-t.c[3]; amp2[i][o]=(t.c[0],t.c[1])
        nr=nv.c[0]; assert nv.c[1]==nv.c[2]==nv.c[3]==0
        for o in range(8): assert sum(amp2[i][o][0] for i in range(8))==nr and sum(amp2[i][o][1] for i in range(8))==0
        fsx=[(0,0),(1,1),(0,1),(1,0)]
        for gg in it.product(range(4),repeat=3):
            s=[sum(amp2[i][B3.index(tuple(fsx[gg[t]][B3[i][t]] for t in range(3)))][c] for i in range(8)) for c in (0,1)]
            assert s==[nr,0]
        tot=(g[64]*nr,Fr(0))
        for r in range(64): i,o=divmod(r,8); tot=(tot[0]+g[r]*amp2[i][o][0],tot[1]+g[r]*amp2[i][o][1])
        sg=sgn(tot); val=(float(tot[0])+float(tot[1])*2**.5)/float(nr)
        print(' orbit',orb,'facet',f,': |v|^2 * (g.p+g0) = %s + %s sqrt2'%tot,'sign',sg,' value %.6f (relative %.6f)'%(val,val/vals[:,f].max()),flush=True)
        assert sg<0; res[orb]=dict(facet=f,value=val,rel=val/float(vals[:,f].max()))
    return res
out=certify(int(sys.argv[1]),[int(x) for x in sys.argv[2].split(',')])
print('EXACT: all listed orbits violated by a purifiable process.')
