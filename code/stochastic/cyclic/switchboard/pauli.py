"""Pauli form of Lemma H.7.1 (switchboard purity). K = C_o C_o'^dag, D = supp(o xor o').
Claim: H.7.1 conditions <=> Pauli coefficients of K vanish on every string X^a Z^b that is non-identity
on every party of D.  Checked here against lemmaC.viol on stored solutions and controls."""
import sys, itertools as it, numpy as np
sys.path.insert(0,'..')
B3=list(it.product((0,1),repeat=3)); IX={t:n for n,t in enumerate(B3)}
X=np.array([[0,1],[1,0]]); Z=np.diag([1,-1]); I2=np.eye(2)
def pstr(a,b):
    M=np.eye(1)
    for k in range(3): M=np.kron(M,np.linalg.matrix_power(X,a[k])@np.linalg.matrix_power(Z,b[k]))
    return M
PAULI={(a,b):pstr(a,b) for a in B3 for b in B3}
def forbidden(D): return [(a,b) for a in B3 for b in B3 if all(a[k] or b[k] for k in D)]
FORB={(o,o2):forbidden([k for k in range(3) if B3[o][k]!=B3[o2][k]]) for o in range(8) for o2 in range(8) if o!=o2}
def resid(C):
    """max |Pauli coeff| over forbidden strings, all ordered pairs"""
    m=0
    for (o,o2),F in FORB.items():
        K=C[o]@C[o2].conj().T
        for ab in F: m=max(m,abs(np.trace(PAULI[ab].conj().T@K))/8)
    return m
if __name__=='__main__':
    import glob
    from lemmaC import viol
    rng=np.random.default_rng(1)
    for f in sorted(glob.glob('../P_*.npy'))+['rand']:
        C=np.array([np.linalg.qr(rng.normal(size=(8,8))+1j*rng.normal(size=(8,8)))[0] for _ in range(8)]) if f=='rand' else np.load(f)
        print(f,'H.7.1 viol %.2e  pauli resid %.2e'%(viol(C),resid(C)))
