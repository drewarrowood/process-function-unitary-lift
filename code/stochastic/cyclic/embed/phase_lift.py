"""H.15.8 [labels per item]: the 'phase lift' of every 3-party binary process function, and the time reverse in the plain frame.
For a PF g (one of the 744 in pfs744.npy, PF[n][i,o] = [i = g(o)]):
 (a) plain time reverse L_g^T: agents' inputs come straight from the past, so in the computational basis p(i|o) = |psi(i)|^2 does not
     depend on o: a mixture of the 8 constant functions, which are PFs (checked to be in the list)  -> always in conv(PF) [PROVED].
 (b) phase lift: U_o^g = Hd diag((-1)^{o.g(z)}) Hd.  By H.15.7e this is (Hadamards on agent wires) o L_g^T, hence pure.
     For each g: max over source states of the violation of each of the 29,344 facets of conv(PF) (as in h13/analyze.py) [NUMERICAL].
Also: is g equivalent to Lugano under party permutations and input/output flips?"""
import numpy as np, itertools as it, gzip, sys
H13='../switchboard/h13/'; F='../../physics/facets/'
PF=np.load('../pfs744.npy'); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]
A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T
assert np.abs(A@T.T-vals).max()<1e-8
Tn=T/vals.max(0)[:,None]
B3=list(it.product((0,1),repeat=3)); ix=B3.index; par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
gs=[tuple(B3[int(np.argmax(PF[n][:,o]))] for o in range(8)) for n in range(744)]
assert all(np.array_equal(PF[n],np.array([[float(ix(gs[n][o])==i) for o in range(8)] for i in range(8)])) for n in range(744))
consts=[n for n in range(744) if len(set(gs[n]))==1]; print('constant PFs present:',len(consts)==8)
lug=lambda o:((1-o[1])*o[2],(1-o[2])*o[0],(1-o[0])*o[1]); xo=lambda u,v:tuple(p^q for p,q in zip(u,v))
def lugeq(g):
    G=lambda o:g[ix(o)]
    for pi in it.permutations(range(3)):
        for fi in B3:
            for fo in B3:
                if all(tuple(G(tuple(o[pi.index(k)]^fo[pi.index(k)] for k in range(3)))[pi[k]]^fi[k] for k in range(3))==lug(o) for o in B3): return True
    return False
f13=lambda z:(z[1]*z[2], z[0]*(1-z[2]), z[0]|z[1])
res=[]
for n,g in enumerate(gs):
    U=np.stack([Hd@np.diag([(-1)**(sum(a*b for a,b in zip(B3[o],g[z]))%2) for z in range(8)])@Hd for o in range(8)])
    P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
    Fm=np.einsum('fr,rst->fst',Tn[:,:64],P)+Tn[:,64,None,None]*np.eye(8)
    v=-np.linalg.eigvalsh(Fm)[:,0]
    res.append((v.max(),lugeq(g),g==tuple(f13(z) for z in B3)))
res=np.array(res,dtype=object)
viol=[n for n in range(744) if res[n][0]>1e-9]; nlug=[n for n in range(744) if res[n][1]]
print('PFs equivalent to Lugano:',len(nlug))
print('PFs whose phase lift leaves conv(PF) (max relative facet violation > 1e-9):',len(viol))
print('  of these Lugano-equivalent:',sum(res[n][1] for n in viol),'; non-Lugano:',[ (n,gs[n],round(float(res[n][0]),4)) for n in viol if not res[n][1]][:20])
print('  Lugano-class max violations:',sorted({round(float(res[n][0]),6) for n in nlug}))
print('  H.13.2 function f present:',[ (n,round(float(res[n][0]),6)) for n in range(744) if res[n][2]])
print('  max violation over non-Lugano PFs:',max([float(res[n][0]) for n in range(744) if not res[n][1]]))
