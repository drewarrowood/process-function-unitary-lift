"""Classify normaliz support hyperplanes of the PF hull into orbits of the 384-element symmetry group.
Input: pf.out (normaliz), Z.npy (744 x 37 PF coords), G.npy (384 x 744 PF permutations), tests.npy (52 x 37 coords).
Canonical form of a facet = lexicographically smallest packed tight-set bitmask over the group."""
import numpy as np, sys, json
Z = np.load('Z.npy').astype(np.int64); G = np.load('G.npy'); T = np.load('tests.npy'); names = json.load(open('test_names.json'))
lines = open('pf.out').read().split('\n')
i = next(k for k, l in enumerate(lines) if l.strip().endswith('support hyperplanes:'))
n = int(lines[i].split()[0]); H = np.array([list(map(int, lines[i + 1 + k].split())) for k in range(n)], dtype=object)
print('facets', n, flush=True)
A = H[:, :37].astype(float); b = H[:, 37].astype(float)          # facet: A.z + b >= 0
tight = (np.abs(Z @ A.T.astype(np.float64) + b) < 1e-6).T                # [n, 744]
Ginv = np.argsort(G, axis=1)                                        # [384, 744]
inv = {}; canon = []
for s in range(0, n, 2000):
    M = tight[s:s + 2000][:, Ginv]                                 # [c, 384, 744]
    K = np.packbits(M, axis=2)                                     # [c, 384, 93]
    V = np.ascontiguousarray(K).view(np.dtype((np.void, K.shape[2])))[..., 0]   # [c, 384]
    mins = np.sort(V, axis=1)[:, 0]
    for m in mins: canon.append(inv.setdefault(m.tobytes(), len(inv)))
    print(s, len(inv), flush=True)
canon = np.array(canon); sizes = np.bincount(canon)
viol = (T @ A.T + b) < -1e-9                                        # [tests, n]
res = dict(n_facets=int(n), n_orbits=len(inv), orbit_sizes=sizes.tolist(),
           violated={nm: sorted(set(canon[viol[j]].tolist())) for j, nm in enumerate(names)},
           tight_count_per_orbit=[int(tight[np.nonzero(canon == c)[0][0]].sum()) for c in range(len(inv))])
json.dump(res, open('classes_full.json', 'w')); print(res['n_facets'], res['n_orbits'])
