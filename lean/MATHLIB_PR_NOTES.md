# Mathlib PR suitability (not opened)

## B. Polar decomposition / trace norm (PFUL/Polar.lean): suitable, after adaptation
Mathlib has `CFC.abs` and `LinearMap.extendOfIsometry` but no polar decomposition on Hilbert space. Minimal PR outline:
1. File `Mathlib/Analysis/InnerProductSpace/PolarDecomposition.lean` (or under `CStarAlgebra/`).
2. `ContinuousLinearMap.norm_abs_apply : ‖CFC.abs T x‖ = ‖T x‖`, `inner_abs_apply_abs_apply`.
3. `ContinuousLinearMap.partialIsometry T` (= `extendOfIsometry` on `(range |T|).topologicalClosure` composed with `orthogonalProjectionOnto`), with lemmas `partialIsometry_comp_abs : V ∘L |T| = T`, `adjoint_partialIsometry_comp_partialIsometry = starProjection`, `partialIsometry_apply_of_mem_orthogonal`, `norm_partialIsometry_le`, `adjoint_partialIsometry_comp_self : V† ∘L T = |T|`.
4. Possibly an `IsPartialIsometry` predicate (V†V is a projection) and uniqueness of the decomposition, which reviewers will probably ask for.
The ‖T‖₁ = Tr|T| part depends on this project's trace-class API, which is not Mathlib's (Mathlib has no trace class yet; there is ongoing Schatten-class work). It would only go in after a trace-class PR.

## A. Born pairing (PFUL/BornPairing.lean): not suitable
It is specific to process functions and ℓ² index conventions. The only generic piece is `hasSum_bornTerm` (∑_r ⟪U†e_r, ρ U†e_r⟫ = Tr(UρU†)). That is a corollary of a trace-class API, not a standalone contribution.

## TraceClass.lean
A trace-class/HS PR would be valuable, but it would have to be reconciled with Mathlib's design (Schatten norms, `HilbertBasis`). Out of scope for now.
