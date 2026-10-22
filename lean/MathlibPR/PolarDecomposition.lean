/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Drew Lamarr Arrowood
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Polar decomposition of bounded operators on a Hilbert space

For a bounded operator `T` on a complex Hilbert space `E`, let `|T| = CFC.abs T = √(T† T)`.
We construct the partial isometry `T.polarIsometry` with

* `ContinuousLinearMap.polarIsometry_comp_abs : T.polarIsometry ∘L CFC.abs T = T`;
* `T.polarIsometry` is isometric on `T.polarInitial = closure (range |T|)` and zero on its
  orthogonal complement;
* `adjoint_polarIsometry_comp_polarIsometry_apply`: `V† V` is the orthogonal projection onto
  `T.polarInitial`; `adjoint_polarIsometry_comp_self : V† ∘L T = |T|`;
* `isPartialIsometry_polarIsometry`, with `ContinuousLinearMap.IsPartialIsometry V : V V† V = V`;
* `ContinuousLinearMap.polar_unique`: uniqueness of the decomposition.

## Implementation notes

The isometry `closure (range |T|) → E`, `|T| x ↦ T x`, is obtained with
`LinearMap.extendOfIsometry`, using `‖ |T| x ‖ = ‖T x‖` (`ContinuousLinearMap.norm_abs_apply`).
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem abs_isPositive (T : E →L[ℂ] E) : (CFC.abs T).IsPositive :=
  nonneg_iff_isPositive.1 (CFC.abs_nonneg T)

theorem abs_comp_abs (T : E →L[ℂ] E) : CFC.abs T ∘L CFC.abs T = adjoint T ∘L T := by
  have := CFC.abs_mul_abs T
  rwa [star_eq_adjoint] at this

theorem adjoint_abs (T : E →L[ℂ] E) : adjoint (CFC.abs T) = CFC.abs T :=
  (abs_isPositive T).isSelfAdjoint.adjoint_eq

theorem inner_abs_apply_abs_apply (T : E →L[ℂ] E) (x y : E) :
    ⟪CFC.abs T x, CFC.abs T y⟫_ℂ = ⟪T x, T y⟫_ℂ := by
  rw [← adjoint_inner_left, adjoint_abs, ← comp_apply, abs_comp_abs, comp_apply,
    adjoint_inner_left]

theorem norm_abs_apply (T : E →L[ℂ] E) (x : E) : ‖CFC.abs T x‖ = ‖T x‖ := by
  have h := inner_abs_apply_abs_apply T x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖CFC.abs T x‖ ^ 2 = ‖T x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

/-- The initial space `closure (range |T|)` of the polar decomposition. -/
noncomputable def polarInitial (T : E →L[ℂ] E) : Submodule ℂ E :=
  (LinearMap.range ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E)).topologicalClosure

instance (T : E →L[ℂ] E) : T.polarInitial.HasOrthogonalProjection := by
  have : CompleteSpace T.polarInitial :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

theorem abs_apply_mem_polarInitial (T : E →L[ℂ] E) (x : E) : CFC.abs T x ∈ T.polarInitial :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E) x)

/-- `x ↦ |T| x` as a map into the initial space. -/
noncomputable def toPolarInitial (T : E →L[ℂ] E) : E →ₗ[ℂ] T.polarInitial :=
  LinearMap.codRestrict T.polarInitial ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E) (abs_apply_mem_polarInitial T)

theorem denseRange_toPolarInitial (T : E →L[ℂ] E) : DenseRange (toPolarInitial T) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro y
  have hy : (y : E) ∈ closure (Set.range (CFC.abs T : E →L[ℂ] E)) := by
    have := y.2
    change (y : E) ∈ ((LinearMap.range ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E)).topologicalClosure : Set E) at this
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at this
  convert hy using 2
  ext z; constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The isometry `closure (range |T|) → E`, `|T| x ↦ T x`. -/
noncomputable def polarIsometryAux (T : E →L[ℂ] E) : T.polarInitial →ₗᵢ[ℂ] E :=
  (T : E →ₗ[ℂ] E).extendOfIsometry (denseRange_toPolarInitial T)
    (fun x => (norm_abs_apply T x).symm)

theorem polarIsometryAux_toPolarInitial (T : E →L[ℂ] E) (x : E) :
    polarIsometryAux T (toPolarInitial T x) = T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- The partial isometry `V` of the polar decomposition `T = V |T|`. -/
noncomputable def polarIsometry (T : E →L[ℂ] E) : E →L[ℂ] E :=
  (polarIsometryAux T).toContinuousLinearMap ∘L T.polarInitial.orthogonalProjectionOnto

/-- **Polar decomposition:** `T = V |T|`. -/
theorem polarIsometry_comp_abs (T : E →L[ℂ] E) : T.polarIsometry ∘L CFC.abs T = T := by
  ext x
  simp only [polarIsometry, comp_apply]
  have : T.polarInitial.orthogonalProjectionOnto (CFC.abs T x) = toPolarInitial T x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (toPolarInitial T x)
  rw [this]; exact polarIsometryAux_toPolarInitial T x

theorem polarIsometry_apply_of_mem (T : E →L[ℂ] E) {x : E} (hx : x ∈ T.polarInitial) :
    T.polarIsometry x = polarIsometryAux T ⟨x, hx⟩ := by
  simp only [polarIsometry, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ : T.polarInitial)]; rfl

theorem polarIsometry_apply_of_mem_orthogonal (T : E →L[ℂ] E) {x : E}
    (hx : x ∈ T.polarInitialᗮ) : T.polarIsometry x = 0 := by
  simp only [polarIsometry, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx]; simp

theorem norm_polarIsometry_apply_of_mem (T : E →L[ℂ] E) {x : E} (hx : x ∈ T.polarInitial) :
    ‖T.polarIsometry x‖ = ‖x‖ := by
  rw [polarIsometry_apply_of_mem T hx, LinearIsometry.norm_map]; rfl

theorem norm_polarIsometry_le (T : E →L[ℂ] E) : ‖T.polarIsometry‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  simp only [polarIsometry, comp_apply, one_mul]
  rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

theorem polarIsometry_apply_starProjection (T : E →L[ℂ] E) (x : E) :
    T.polarIsometry (T.polarInitial.starProjection x) = T.polarIsometry x := by
  have hx : x = T.polarInitial.starProjection x + (x - T.polarInitial.starProjection x) := by abel
  conv_rhs => rw [hx, map_add]
  rw [polarIsometry_apply_of_mem_orthogonal T
    (T.polarInitial.sub_starProjection_mem_orthogonal x), add_zero]

/-- `V† V` is the orthogonal projection onto the initial space. -/
theorem adjoint_polarIsometry_comp_polarIsometry_apply (T : E →L[ℂ] E) (x : E) :
    adjoint T.polarIsometry (T.polarIsometry x) = T.polarInitial.starProjection x := by
  set K := T.polarInitial
  refine ext_inner_left ℂ fun y => ?_
  rw [adjoint_inner_right, ← polarIsometry_apply_starProjection T y,
    ← polarIsometry_apply_starProjection T x, polarIsometry_apply_of_mem T (K.starProjection_apply_mem y),
    polarIsometry_apply_of_mem T (K.starProjection_apply_mem x), LinearIsometry.inner_map_map]
  change ⟪K.starProjection y, K.starProjection x⟫_ℂ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    K.starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]

/-- `V† T = |T|`. -/
theorem adjoint_polarIsometry_comp_self (T : E →L[ℂ] E) :
    adjoint T.polarIsometry ∘L T = CFC.abs T := by
  ext x
  have h : T x = T.polarIsometry (CFC.abs T x) := by rw [← comp_apply, polarIsometry_comp_abs]
  rw [comp_apply, h, adjoint_polarIsometry_comp_polarIsometry_apply]
  exact T.polarInitial.starProjection_eq_self_iff.2 (abs_apply_mem_polarInitial T x)

/-- A partial isometry: `V V† V = V`. -/
def IsPartialIsometry (V : E →L[ℂ] E) : Prop := V ∘L adjoint V ∘L V = V

theorem IsPartialIsometry.adjoint_comp_self_idempotent {V : E →L[ℂ] E} (hV : IsPartialIsometry V) :
    (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L V := by
  have : (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L (V ∘L adjoint V ∘L V) := by
    simp only [comp_assoc]
  rw [this, hV]

theorem isPartialIsometry_polarIsometry (T : E →L[ℂ] E) : IsPartialIsometry T.polarIsometry := by
  ext x
  simp only [comp_apply]
  rw [adjoint_polarIsometry_comp_polarIsometry_apply, polarIsometry_apply_starProjection]

/-- **Uniqueness of the polar decomposition.** If `T = W A` with `A` positive, `W` isometric on
`range A` and zero on `(range A)ᗮ`, then `A = |T|` and `W = T.polarIsometry`. -/
theorem polar_unique {T W A : E →L[ℂ] E} (hA : A.IsPositive) (hT : W ∘L A = T)
    (hWiso : ∀ x, ‖W (A x)‖ = ‖A x‖)
    (hW0 : ∀ x ∈ (LinearMap.range (A : E →ₗ[ℂ] E))ᗮ, W x = 0) :
    A = CFC.abs T ∧ W = T.polarIsometry := by
  have hAA : adjoint T ∘L T = A ∘L A := by
    have hz : ∀ x, ⟪(adjoint T ∘L T - A ∘L A) x, x⟫_ℂ = 0 := by
      intro x
      rw [sub_apply, inner_sub_left, comp_apply, adjoint_inner_left, comp_apply,
        ← adjoint_inner_right A, hA.isSelfAdjoint.adjoint_eq, ← hT, comp_apply,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hWiso, sub_self]
    have := (inner_map_self_eq_zero ((adjoint T ∘L T - A ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E)).1 hz
    exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective this)
  have hA' : A = CFC.abs T := by
    have h0 : 0 ≤ A := nonneg_iff_isPositive.2 hA
    change A = CFC.sqrt (star T * T)
    rw [star_eq_adjoint]
    change A = CFC.sqrt (adjoint T ∘L T)
    rw [hAA]
    exact (CFC.sqrt_mul_self A h0).symm
  refine ⟨hA', ?_⟩
  subst hA'
  set K := T.polarInitial
  have hrange : LinearMap.range ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤
      LinearMap.ker ((W - T.polarIsometry : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply]
    rw [← comp_apply W, hT, ← comp_apply T.polarIsometry, polarIsometry_comp_abs, sub_self]
  have hK : K ≤ LinearMap.ker ((W - T.polarIsometry : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
    Submodule.topologicalClosure_minimal _ hrange (W - T.polarIsometry).isClosed_ker
  ext x
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  have horth : x - K.starProjection x ∈ (LinearMap.range ((CFC.abs T : E →L[ℂ] E) : E →ₗ[ℂ] E))ᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure _)
      (K.sub_starProjection_mem_orthogonal x)
  have h1 := hK (K.starProjection_apply_mem x)
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, sub_eq_zero] at h1
  rw [hx, map_add, map_add, h1, hW0 _ horth,
    polarIsometry_apply_of_mem_orthogonal T (K.sub_starProjection_mem_orthogonal x)]

end ContinuousLinearMap
