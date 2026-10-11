# Algebraic-geometry route for AFNB Thm 4 (orbit 8): size estimates and feasibility (Oct 10 2026)

Question: is there a 16-dim complex subspace W of V_W with w^dagger Q_t w' = 0 for all w, w' in W and all forms Q_t?

The system is not complex-algebraic. The forms are sesquilinear (conjugate-linear in one argument), so as a
polynomial system it lives over the reals: write W = Re + i Im in Grassmannian chart coordinates.

Sizes (forms counted after dropping redundant ones, i.e. dim of the form span from gpusearch.prep):

| case   | m = dim V_W | r  | independent forms K | chart unknowns (real) | real quadratic equations K*2r^2 |
|--------|-------------|----|---------------------|-----------------------|---------------------------------|
| E_ex1  | 27          | 16 | 46                  | 2*16*11 = 352         | 23,552                          |
| orbit 8| 82          | 16 | 196                 | 2*16*66 = 2,112       | 100,352                         |

Feasibility.
- Homotopy continuation (HomotopyContinuation.jl / Bertini) has to square up the system: n random combinations in n
  unknowns. The total-degree start system then has 2^n paths: 2^352 for E_ex1 and 2^2112 for orbit 8. Polyhedral or
  monodromy methods do not help for a system with no solutions, which is exactly the case to be certified.
  Infeasible, even for the validation case.
- Groebner bases (msolve/Singular/M2) in hundreds to thousands of real variables: far beyond any known computation
  (practical limits are tens of variables for dense quadratic systems). Infeasible.
- Symmetry (stabiliser order 8 for orbit 8) does not reduce the unknowns, because W need not be invariant. At best it
  splits the search into orbits of solutions, which does not help to prove that none exist.
- Small sub-problems are feasible in size but not informative. For r = 1 the vector c0 is always a solution. For
  r = 2..4 E_ex1 has isotropic subspaces (numerically, App. E), so these sub-problems only reproduce existence.
  Non-existence first appears near r = 15-16, where the full size applies.

Tools: none installed (julia, Singular, Macaulay2, msolve and Bertini are absent; no conda or sudo on the box).
Given the counts above, installing them would not change the conclusion.

Conclusion: exact or numerical algebraic geometry on the full Theorem 4 system is infeasible for orbit 8, and also
for the E_ex1 validation case. Exact certificates for the open orbits need a structural argument (or a stronger
convex hierarchy, App. E), not brute-force elimination.
