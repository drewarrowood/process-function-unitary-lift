"""Exact no-ancilla purity condition for family C (Lemma H.7.2): for all o != o' and delta,
with K = C_o C_o'^dag, D = supp(o xor o'), S = D minus supp(delta):
  sum_{e_S} (-1)^{|e_S|} K[e, e xor delta] = 0 for every value of e outside S.
Prints the max violation for the stored solutions and for random C (control)."""
import sys, glob, numpy as np, itertools as it
B3=list(it.product((0,1),repeat=3)); IX={t:n for n,t in enumerate(B3)}
def viol(C):
    m=0
    for o in range(8):
        for o2 in range(8):
            if o==o2: continue
            K=C[o]@C[o2].conj().T; D=[k for k in range(3) if B3[o][k]!=B3[o2][k]]
            for d in B3:
                S=[k for k in D if d[k]==0]; rest=[k for k in range(3) if k not in S]
                for er in it.product((0,1),repeat=len(rest)):
                    tot=0
                    for es in it.product((0,1),repeat=len(S)):
                        e=[0]*3
                        for k,v in zip(rest,er): e[k]=v
                        for k,v in zip(S,es): e[k]=v
                        e=tuple(e); e2=tuple(a^b for a,b in zip(e,d))
                        tot+=(-1)**sum(es)*K[IX[e],IX[e2]]
                    m=max(m,abs(tot))
    return m
lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
C=np.zeros((8,8,8))
for o in B3:
    for e in B3: C[IX[o],IX[tuple(a^b for a,b in zip(lug(o),e))],IX[e]]=1
print('lugano',viol(C))
rng=np.random.default_rng(0)
R=np.array([np.linalg.qr(rng.normal(size=(8,8))+1j*rng.normal(size=(8,8)))[0] for _ in range(8)]); print('random',viol(R))
for f in sorted(glob.glob(sys.argv[1] if len(sys.argv)>1 else 'P_*.npy')): print(f,viol(np.load(f)))
