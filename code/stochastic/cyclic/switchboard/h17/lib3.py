"""Shared tools for H.17.  Conventions (msb = party 0 everywhere):
vertex/output string o in 0..7, basis/input string i in 0..7, bit (2-t) <-> party t.
Pauli string s = (x,z) encoded as x | z<<3 (x,z in 0..7, same bit convention); matrix X^x Z^z, X^x|j> = |j xor x>.
Pauli rule (H.8.1): for o != q with D = o xor q, (x,z) is forbidden iff ((x|z) & D) == D."""
import numpy as np, itertools as it, gzip
X1=np.array([[0,1],[1,0]],complex); Z1=np.diag([1.,-1.]).astype(complex); I1=np.eye(2,dtype=complex)
def px(s): return s&7
def pz(s): return s>>3
def pmat(s):
    x,z=px(s),pz(s); M=np.array([[1.+0j]])
    for t in range(3):
        b=2-t; m=I1
        if (x>>b)&1: m=X1@m if False else X1
        if (z>>b)&1: m=(X1 if (x>>b)&1 else I1)@Z1
        M=np.kron(M,m)
    return M
PM=np.array([pmat(s) for s in range(64)])
def herm(s):            # Hermitian version of the Pauli string (Y-type factors need a factor i)
    ny=bin(px(s)&pz(s)).count('1'); return PM[s]*(1j**ny)
HM=np.array([herm(s) for s in range(64)])
def anti(s,t): return (bin(px(s)&pz(t)).count('1')+bin(pz(s)&px(t)).count('1'))%2
def forbidden(s,D): return ((px(s)|pz(s))&D)==D
FORB=np.array([[forbidden(s,D) if D else False for s in range(64)] for D in range(8)])
def pauli_coeffs(K): return np.einsum('sij,ij->s',PM.conj(),K)/8
def rule_residual(U):
    r=0.
    for o in range(8):
        for q in range(o+1,8):
            c=pauli_coeffs(U[o]@U[q].conj().T); r+=np.sum(np.abs(c[FORB[o^q]])**2)
    return r
# facets
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float)            # [744,i,o]
def load_facets():
    Zc=np.load(F+'Z.npy').astype(float)
    L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
    Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
    vals=Zc@Hm[:,:37].T+Hm[:,37]
    T=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals,rcond=None)[0].T/vals.max(0)[:,None]
    canon=np.load('../h13/xviol.npz')['canon'].astype(int)
    return T,canon
def projectors(U):  # P[i*8+o] = U_o^dag |i><i| U_o
    return np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
def facet_viol(U,T):
    """relative violation of every facet, maximised over source states (positive = outside conv(PF))"""
    P=projectors(U)
    return -np.linalg.eigvalsh(np.einsum('fr,rst->fst',T[:,:64],P)+T[:,64,None,None]*np.eye(8))[:,0]
NC=[4,5,6,7,8,9,10,11,14,25,26,28,30,31,53,54,57,66,69,75,79,81,92]
