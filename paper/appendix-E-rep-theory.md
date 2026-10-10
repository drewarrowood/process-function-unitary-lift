
## E.5 Validation result (Oct 10 2026): the relaxation is too weak

Symmetry reduction turned out to be unnecessary for this test. For E_ex1 (m = 27, r = 16) the unreduced relaxation
(Y of size 729) is small enough to solve directly by cyclic projections in complex arithmetic
(`code/stochastic/rep/pocs.py`). The solver was checked on a positive control: it converges to feasibility at r = 1
(witness c0) and at r = 2, 4. At r = 4 a direct search (isotest) independently finds a 4-dim isotropic subspace
(loss 1.6e-10 and falling).

**At r = 16 the full E.2 relaxation is feasible for E_ex1, which is known to be non-purifiable.** The point found
(`PY_eex1_r16.npz`) satisfies all affine constraints to about 1e-13. Every cone constraint holds with strict margin:
min eig Y = 0.13, eig P in [0.58, 0.63], tr P = 16, min eig of P (x) I - Y = 0.019. The feasibility is therefore
robust, not a numerical artefact. So the degree-2-in-P moment relaxation cannot certify even E_ex1. The single-form
inertia certificate does certify E_ex1 (bound 14 < 16), so this relaxation is strictly weaker than that test here.
Its P is nearly a multiple of the identity, about (16/27)·I: it does not see rank.

Consequences. Symmetry-reducing this relaxation is pointless, and the isotypic block decomposition was not built.
Lugano was not run: it is purifiable, so it is feasible anyway. A useful convex certificate must encode rank or
projector structure more strongly, for example higher moment levels (P^{(x)3} and beyond, sizes m^6), or must combine
the inertia argument with a lift. Recommendation: stop the moment route at this level. Prefer either an exact
algebraic or Groebner computation on symmetry-reduced small cases, or accept numerical evidence for the open orbits.
