# Better certificates for orbits 8/10/20 (dim V_W 82, r 16): findings (Oct 10 2026)

1. Block (matrix-valued) inertia test (blocksearch.py), sound: W isotropic => W(x)C^k isotropic for any Hermitian block
   form whose blocks are constraint forms, so rk <= n0+min(n+,n-). Generalises single-form (k=1). Validated: orbit7
   certified (k=2, bound 14), Lugano not (21.5). Orbits 8/10/20, k=2: NOT certified (best bound/k 20.5; warm start
   from k=1 got worse, 28). Objective plateaus at lambda_rk ~ +1e-4, same as k=1.
2. Pure-isotropy feasibility (isotest.py): minimise sum_ij ||L3perp(X(c_i) Lam X(c_j)^H)||^2 over orthonormal r-frames.
   Lugano -> 4e-20 (isotropic 8-plane exists, as it must); orbit7 stalls ~5.6; orbit8 stalls at 2.3398 (1 restart,
   1400 steps). So numerically no isotropic 16-plane exists for orbit 8: an isotropy-only certificate should exist,
   but linear (single/block Hermitian form, i.e. SDP-dual-type) families appear to have a duality gap here.
3. Fixed-vector trick: K(c0) = {Y c0} is identically 0 on V_W (proved: X_a Lam W = X_a, <psi, X_a> = 0), no gain.
   Generic vector w: rank K(w) = m-1 (all three test cases), so the obstruction lives on the special set of jointly
   isotropic vectors; a certificate "every jointly isotropic w has rank K(w) > m-r" is sound but algebraic (open).
4. Not done: symmetry reduction (stabiliser block-diagonalisation; sound for reducing the SIZE of forms/relaxations,
   NOT for assuming W invariant), Kronecker pencil bounds, degree-4 SOS on the Stiefel manifold (1312 complex vars,
   infeasible without symmetry reduction), combinatorial physics argument.
