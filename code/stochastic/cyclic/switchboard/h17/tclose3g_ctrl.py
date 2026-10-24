"""Controls for tclose3g on the two known three-class tuned boards (tb_*.npz with 3 classes): with their actual pair supports,
the loosened solver must find a board (the real board is representable) and the real solver must find no counterexample."""
import glob, numpy as np, tclose3g as T
from lib3 import PM, pauli_coeffs
def supp(K): c=pauli_coeffs(K); return tuple(s for s in range(64) if abs(c[s])>1e-9)
for f in sorted(glob.glob('tb_*.npz')):
    d=np.load(f); U=d['U']; P=d['P']; k=d['k']; ks=sorted(set(k.tolist()))
    if len(ks)!=3: continue
    V={int(k[o]):PM[P[o]].conj().T@U[o] for o in range(8)}
    a,b,c=ks; job=(supp(V[b]@V[a].conj().T),supp(V[c]@V[a].conj().T),supp(V[c]@V[b].conj().T))
    print(f,'supports',job,'loosened:',T.solve(job,loosen=True) is not None,'real counterexample:',T.solve(job))
