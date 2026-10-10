# Stochastic classical processes: numerics

These scripts test AFNB 2017 Theorem 4 (the purifiability criterion) numerically. They use 3 parties with binary inputs and outputs. The sink F' is modelled as a 4th party with trivial output.

- `vert.py`: checks that E_ex1 = (C + C̄)/2 is logically consistent and is a vertex of the Baumeler–Wolf polytope (C is the circular identity, C̄ the circular bit-flip). Active constraints have rank 64 of 64.
- `vw.py`: computes dim V_W, the space where AFNB's linear necessary condition holds. Results (rank, dim V_W): Lugano (8, 56); mixture const+chain (14, 242); E_ex1 (16, 27); C alone (8, 0), as expected for an inconsistent process.
- `kern.py` and `iso.py`: E_ex1 reduced to the quadratic conditions. Purifiability needs a 16-dim subspace S of C^27 containing c0 on which 46 sesquilinear forms vanish. Each form's Hermitian part admits totally isotropic subspaces of dimension at most 12. Spectral gaps: about 1e-17 versus 5e-3.
- `ctrl.py`: the same pipeline on Lugano, a known purifiable control. Bound 29 ≥ rank 8, so no contradiction.

Runtime is about 10–25 min per process on one core.
