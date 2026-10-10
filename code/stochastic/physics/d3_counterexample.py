"""Counterexample to Conjecture D.3 (single classical source basis), for a causally ordered unitary process.
Parties: A (input trivial, output oA in {0,1}), then B (input iB, output oB).  Source P = m (x) a (two qubits).
Circuit: apply H^{oA} to m, CNOT m -> a, send m to B's input, sink F = (oA, oB, a).
V|m,a,oA,oB> = sum_x <x|H^{oA}|m> |iB=x> (x) |oA, oB, x xor a>.  A causally ordered circuit of unitaries, so it is
a valid unitary process (AFNB).  With psi=|00>, W is classical: p(iB|oA=0)=delta_{iB,0}, p(iB|oA=1)=1/2 (a mixture of
process functions).  But G_{i,o} = Vo^dag (Pi_i (x) 1) Vo on P are projectors that do NOT commute across o, so no
single source basis makes every V|lambda,o> classical on the party inputs: D.3 fails, the mixture conclusion holds."""
import numpy as np, itertools as it
H = np.array([[1, 1], [1, -1]]) / np.sqrt(2); I2 = np.eye(2)
def Vcol(m, a, oA, oB):              # returns vector in I_B (2) x F (oA 2, oB 2, a' 2) = 16
    out = np.zeros(16)
    U = np.linalg.matrix_power(H, oA)
    for x in range(2):
        f = (oA * 2 + oB) * 2 + (x ^ a); out[x * 8 + f] += U[x, m]
    return out
cols = [(m, a, oA, oB) for m, a, oA, oB in it.product(range(2), repeat=4)]
V = np.stack([Vcol(*c) for c in cols], 1)
print('V unitary:', np.allclose(V.T @ V, np.eye(16)))
# classical process with psi = |m=0,a=0>
for oA in range(2):
    for oB in range(2):
        out = Vcol(0, 0, oA, oB).reshape(2, 8)
        print('p(iB | oA=%d, oB=%d) =' % (oA, oB), np.round((out ** 2).sum(1), 3))
# Choi coherences: v_{o,i} orthogonal (Lemma D.1)
v = {(oA, oB, i): Vcol(0, 0, oA, oB).reshape(2, 8)[i] for oA, oB, i in it.product(range(2), repeat=3)}
G = np.array([[v[x] @ v[y] for y in v] for x in v]); print('W diagonal:', np.allclose(G, np.diag(np.diag(G))))
# G_{i,o} on P (4-dim)
def Gop(i, oA, oB):
    Vo = np.stack([Vcol(m, a, oA, oB) for m, a in it.product(range(2), repeat=2)], 1).reshape(2, 8, 4)
    return Vo[i].T @ Vo[i]
Gs = {(i, oA, oB): Gop(i, oA, oB) for i, oA, oB in it.product(range(2), repeat=3)}
print('all projectors:', all(np.allclose(g @ g, g) for g in Gs.values()))
print('max commutator norm:', max(np.abs(g @ h - h @ g).max() for g in Gs.values() for h in Gs.values()))
