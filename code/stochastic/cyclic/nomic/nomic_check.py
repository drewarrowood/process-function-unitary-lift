"""Is the H.13.2 correlation antinomic in the sense of Kunjwal-Oreshkov (arXiv:2307.02565)?

Scenario (3,2,2): three parties, binary settings a_k and binary outcomes x_k.
Correlation tested: P(x|a) := p(i=x | o=a), with p the H.13.2 process (identity
classical instruments: output the setting, report the input).

Nomic vertices (K-O Thm 4): deterministic f: a -> x such that the faithful map
g_k(a_\\k) := (f_k(0,a_\\k), f_k(1,a_\\k)) (|I_k| <= 4) is a process function.
PF test: every deterministic intervention h_k: I_k -> {0,1} has exactly one fixed point.

Checks:
 (0) p is valid (all 64 binary deterministic interventions give total probability 1).
 (1) sanity: max of K-O's GYNIN score over nomic vertices is 5/8 (their Eq. (102)).
 (2) LP (HiGHS): p lies in the convex hull of the nomic vertices.
 (3) exact: the LP support is re-solved in Fraction arithmetic; weights are
     nonnegative rationals summing to 1 and reproduce p exactly.
"""
import itertools
from fractions import Fraction as F
import numpy as np, scipy.sparse as sp
from scipy.optimize import linprog
import sympy

def bits(n): return ((n >> 2) & 1, (n >> 1) & 1, n & 1)
def idx(b): return (b[0] << 2) | (b[1] << 1) | b[2]
def rest(a, k):
    b = bits(a); r = [b[j] for j in range(3) if j != k]; return 2 * r[0] + r[1]

# --- H.13.2 process, exact (paper/lift.md H.13.2) ---
ROWS = ["00000000", "00111111", "00001010", "00110101",
        "00010001", "00101110", "00011011", "00100100"]
N = [[int(c) for c in r] for r in ROWS]
phi = [F(1, 2), F(1, 2), F(1, 2), 0, 0, F(-1, 2), 0, 0]
def had8(z, w):  # (H^{x3})_{z,w} * sqrt(8)
    return (-1) ** bin(z & w).count("1")
p = [[F(0)] * 8 for _ in range(8)]  # p[o][i]
for o in range(8):
    # U_o = Hd diag((-1)^n) Hd, entries (1/8) sum_z had(i,z)(-1)^n(z) had(z,j)
    psi = []
    for i in range(8):
        s = F(0)
        for j in range(8):
            u = F(sum(had8(i, z) * (-1) ** N[o][z] * had8(z, j) for z in range(8)), 8)
            s += u * phi[j]
        psi.append(s)
    p[o] = [x * x for x in psi]
for h in itertools.product(range(4), repeat=3):
    tot = sum(p[idx(tuple((h[k] >> bits(i)[k]) & 1 for k in range(3)))][i] for i in range(8))
    assert tot == 1
print("(0) H.13.2 p valid (exact); entries x16:")
for o in range(8): print("   ", [int(16 * x) for x in p[o]])

# --- nomic vertices ---
def part_of(fk, k):
    out = []
    for r in range(4):
        out.append(tuple((fk >> a) & 1 for ak in (0, 1) for a in range(8)
                         if bits(a)[k] == ak and rest(a, k) == r))
    m = {}; return tuple(m.setdefault(v, len(m)) for v in out)
parts = [{} for _ in range(3)]
for k in range(3):
    for fk in range(256): parts[k].setdefault(part_of(fk, k), []).append(fk)
def isPF(P):
    sizes = [max(P[k]) + 1 for k in range(3)]
    for hs in itertools.product(*[range(2 ** s) for s in sizes]):
        n = sum(all(((hs[k] >> P[k][rest(a, k)]) & 1) == bits(a)[k] for k in range(3)) for a in range(8))
        if n != 1: return False
    return True
good = [P for P in itertools.product(*[list(parts[k]) for k in range(3)]) if isPF(P)]
V = []
for P in good:
    for f in itertools.product(*[parts[k][P[k]] for k in range(3)]):
        v = np.zeros((8, 8))
        for a in range(8): v[a, idx(tuple((f[k] >> a) & 1 for k in range(3)))] = 1
        V.append(v.ravel())
V = np.array(V)
print(f"nomic vertices in (3,2,2): {len(V)} (from {len(good)} PF partition triples)")

g = np.zeros((8, 8))
for a in range(8):
    b = bits(a)
    g[a, idx((b[2], b[0], b[1]))] += 1 / 8; g[a, idx((1 - b[2], 1 - b[0], 1 - b[1]))] += 1 / 8
print("(1) max GYNIN over nomic vertices:", (V @ g.ravel()).max(), "(K-O bound 5/8 = 0.625)")

pv = np.array([[float(x) for x in row] for row in p]).ravel()
n = len(V)
A = sp.csr_matrix(np.vstack([V.T, np.ones((1, n))]))
r = linprog(np.zeros(n), A_eq=A, b_eq=np.concatenate([pv, [1]]), bounds=(0, None), method="highs")
print("(2) LP membership status:", r.status, r.message)
S = [j for j in range(n) if r.x[j] > 1e-9]
print("    support size:", len(S))

M = sympy.Matrix([[int(V[j][e]) for j in S] for e in range(64)] + [[1] * len(S)])
bb = sympy.Matrix([sympy.Rational(x.numerator, x.denominator) for row in p for x in row] + [1])
sol, params = M.gauss_jordan_solve(bb)
sol = sol.subs({t: 0 for t in params})
assert M * sol == bb and all(x >= 0 for x in sol)
print("(3) exact rational decomposition: weights >= 0, sum 1, reproduces p exactly:",
      sorted(set(str(x) for x in sol)))
print("CONCLUSION: the H.13.2 correlation (identity instruments) is NOMIC; it does not answer K-O's question.")
