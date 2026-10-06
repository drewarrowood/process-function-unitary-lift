"""Numerical certificate for the source-sink lift of the Lugano process function.

The permutation unitary of the reversible extension induces a unitary source-to-sink
map when each party inserts a unitary. Lugano passes. A non-process (swap-like)
fails. This is a check, not the proof. The proof is the combinatorial lemma in paper/lift.md.
"""

import numpy as np
from itertools import product


def lugano(o):
    a, b, c = o
    return ((1 - b) & c, (1 - c) & a, (1 - a) & b)


def bad(o):
    a, b, c = o
    return (b, a, 0)


def idx(bits):
    return sum(int(b) << i for i, b in enumerate(bits))


def induced(w, Vs):
    n = len(Vs)
    M = np.zeros((2**n, 2**n), dtype=complex)
    for e in product((0, 1), repeat=n):
        for o in product((0, 1), repeat=n):
            i = tuple(w(o)[k] ^ e[k] for k in range(n))
            amp = 1.0
            for k in range(n):
                amp *= Vs[k][o[k], i[k]]
            M[idx(o), idx(e)] += amp
    return M


def deviation(M):
    d = M.shape[0]
    return np.linalg.norm(M @ M.conj().T - np.eye(d))


def randU(rng):
    z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    q, r = np.linalg.qr(z)
    d = np.diag(r)
    return q * (d / np.abs(d))


def main():
    H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
    I2 = np.eye(2, dtype=complex)
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    for name, Vs in [
        ("III", [I2, I2, I2]),
        ("XXX", [X, X, X]),
        ("HHH", [H, H, H]),
    ]:
        print(f"Lugano {name}: {deviation(induced(lugano, Vs)):.3e}")

    rng = np.random.default_rng(0)
    maxdev = 0.0
    for _ in range(30):
        Vs = [randU(rng), randU(rng), randU(rng)]
        maxdev = max(maxdev, deviation(induced(lugano, Vs)))
    print(f"Lugano 30 random product unitaries, max deviation: {maxdev:.3e}")

    max_bad = 0.0
    for _ in range(10):
        Vs = [randU(rng), randU(rng), randU(rng)]
        max_bad = max(max_bad, deviation(induced(bad, Vs)))
    print(f"non-process swap-like, max deviation: {max_bad:.3e}")


if __name__ == "__main__":
    main()
