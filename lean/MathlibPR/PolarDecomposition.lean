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
# Polar decomposition of bounded operators between Hilbert spaces

Let `T : E →L[ℂ] F` be a bounded operator between complex Hilbert spaces.

## Main definitions

* `ContinuousLinearMap.polarAbs T : E →L[ℂ] E`: the absolute value `|T| = √(T† T)`.
  For `T : E →L[ℂ] E` it agrees with `CFC.abs T` (`ContinuousLinearMap.polarAbs_eq_abs`).
* `ContinuousLinearMap.polarInitial T`: the initial space `closure (range |T|)`.
* `ContinuousLinearMap.polarIsometry T : E →L[ℂ] F`: the partial isometry of the polar
  decomposition.
* `ContinuousLinearMap.IsPartialIsometry V`: `V V† V = V`.

## Main results

* `ContinuousLinearMap.polarIsometry_comp_polarAbs`: `T = V |T|`.
* `ContinuousLinearMap.adjoint_polarIsometry_comp_polarIsometry_apply`: `V† V` is the orthogonal
  projection onto the initial space.
* `ContinuousLinearMap.ker_polarIsometry`: `ker V = ker T`.
* `ContinuousLinearMap.polar_unique`: uniqueness of the decomposition.

## Implementation notes

The isometry `closure (range |T|) → F`, `|T| x ↦ T x`, is built with
`LinearMap.extendOfIsometry` from `‖ |T| x ‖ = ‖T x‖` (`ContinuousLinearMap.norm_polarAbs_apply`).
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The absolute value `|T| = √(T† T)` of a bounded operator between Hilbert spaces. -/
noncomputable def polarAbs (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (adjoint T ∘L T)

theorem polarAbs_eq_abs (T : E →L[ℂ] E) : T.polarAbs = CFC.abs T := by
  rw [polarAbs, CFC.abs, star_eq_adjoint]; rfl

theorem polarAbs_nonneg (T : E →L[ℂ] F) : 0 ≤ T.polarAbs := CFC.sqrt_nonneg _

theorem isPositive_polarAbs (T : E →L[ℂ] F) : T.polarAbs.IsPositive :=
  nonneg_iff_isPositive.1 (polarAbs_nonneg T)

@[simp]
theorem polarAbs_comp_polarAbs (T : E →L[ℂ] F) : T.polarAbs ∘L T.polarAbs = adjoint T ∘L T :=
  CFC.sqrt_mul_sqrt_self _ (nonneg_iff_isPositive.2 (isPositive_adjoint_comp_self T))

@[simp]
theorem adjoint_polarAbs (T : E →L[ℂ] F) : adjoint T.polarAbs = T.polarAbs :=
  (isPositive_polarAbs T).isSelfAdjoint.adjoint_eq

theorem inner_polarAbs_apply_polarAbs_apply (T : E →L[ℂ] F) (x y : E) :
    ⟪T.polarAbs x, T.polarAbs y⟫_ℂ = ⟪T x, T y⟫_ℂ := by
  rw [← adjoint_inner_left, adjoint_polarAbs, ← comp_apply, polarAbs_comp_polarAbs, comp_apply,
    adjoint_inner_left]

@[simp]
theorem norm_polarAbs_apply (T : E →L[ℂ] F) (x : E) : ‖T.polarAbs x‖ = ‖T x‖ := by
  have h := inner_polarAbs_apply_polarAbs_apply T x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖T.polarAbs x‖ ^ 2 = ‖T x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

theorem polarAbs_apply_eq_zero_iff (T : E →L[ℂ] F) (x : E) : T.polarAbs x = 0 ↔ T x = 0 := by
  rw [← norm_eq_zero, norm_polarAbs_apply, norm_eq_zero]

theorem ker_polarAbs (T : E →L[ℂ] F) :
    LinearMap.ker (T.polarAbs : E →ₗ[ℂ] E) = LinearMap.ker (T : E →ₗ[ℂ] F) := by
  ext x; simp [polarAbs_apply_eq_zero_iff]

/-- The initial space `closure (range |T|)` of the polar decomposition. -/
noncomputable def polarInitial (T : E →L[ℂ] F) : Submodule ℂ E :=
  (LinearMap.range (T.polarAbs : E →ₗ[ℂ] E)).topologicalClosure

instance (T : E →L[ℂ] F) : T.polarInitial.HasOrthogonalProjection := by
  have : CompleteSpace T.polarInitial :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

theorem polarAbs_apply_mem_polarInitial (T : E →L[ℂ] F) (x : E) :
    T.polarAbs x ∈ T.polarInitial :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (T.polarAbs : E →ₗ[ℂ] E) x)

theorem polarInitial_orthogonal (T : E →L[ℂ] F) :
    T.polarInitialᗮ = LinearMap.ker (T : E →ₗ[ℂ] F) := by
  rw [polarInitial, ← Submodule.orthogonal_orthogonal_eq_closure,
    Submodule.triorthogonal_eq_orthogonal, ← ker_polarAbs]
  have := orthogonal_range T.polarAbs
  rw [adjoint_polarAbs] at this
  exact this

/-- `x ↦ |T| x` as a map into the initial space. -/
noncomputable def toPolarInitial (T : E →L[ℂ] F) : E →ₗ[ℂ] T.polarInitial :=
  LinearMap.codRestrict T.polarInitial (T.polarAbs : E →ₗ[ℂ] E)
    (polarAbs_apply_mem_polarInitial T)

theorem denseRange_toPolarInitial (T : E →L[ℂ] F) : DenseRange (toPolarInitial T) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro y
  have hy : (y : E) ∈ closure (Set.range T.polarAbs) := by
    have := y.2
    change (y : E) ∈ ((LinearMap.range (T.polarAbs : E →ₗ[ℂ] E)).topologicalClosure : Set E)
      at this
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at this
  convert hy using 2
  ext z; constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The isometry `closure (range |T|) → F`, `|T| x ↦ T x`. -/
noncomputable def polarIsometryAux (T : E →L[ℂ] F) : T.polarInitial →ₗᵢ[ℂ] F :=
  (T : E →ₗ[ℂ] F).extendOfIsometry (denseRange_toPolarInitial T)
    (fun x => (norm_polarAbs_apply T x).symm)

theorem polarIsometryAux_toPolarInitial (T : E →L[ℂ] F) (x : E) :
    polarIsometryAux T (toPolarInitial T x) = T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- The partial isometry `V` of the polar decomposition `T = V |T|`. -/
noncomputable def polarIsometry (T : E →L[ℂ] F) : E →L[ℂ] F :=
  (polarIsometryAux T).toContinuousLinearMap ∘L T.polarInitial.orthogonalProjectionOnto

/-- **Polar decomposition:** `T = V |T|`. -/
@[simp]
theorem polarIsometry_comp_polarAbs (T : E →L[ℂ] F) : T.polarIsometry ∘L T.polarAbs = T := by
  ext x
  simp only [polarIsometry, comp_apply]
  have : T.polarInitial.orthogonalProjectionOnto (T.polarAbs x) = toPolarInitial T x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (toPolarInitial T x)
  rw [this]; exact polarIsometryAux_toPolarInitial T x

@[simp]
theorem polarIsometry_polarAbs_apply (T : E →L[ℂ] F) (x : E) :
    T.polarIsometry (T.polarAbs x) = T x := by
  rw [← comp_apply, polarIsometry_comp_polarAbs]

theorem polarIsometry_apply_of_mem (T : E →L[ℂ] F) {x : E} (hx : x ∈ T.polarInitial) :
    T.polarIsometry x = polarIsometryAux T ⟨x, hx⟩ := by
  simp only [polarIsometry, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ : T.polarInitial)]; rfl

theorem polarIsometry_apply_of_mem_orthogonal (T : E →L[ℂ] F) {x : E}
    (hx : x ∈ T.polarInitialᗮ) : T.polarIsometry x = 0 := by
  simp only [polarIsometry, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx]; simp

theorem norm_polarIsometry_apply_of_mem (T : E →L[ℂ] F) {x : E} (hx : x ∈ T.polarInitial) :
    ‖T.polarIsometry x‖ = ‖x‖ := by
  rw [polarIsometry_apply_of_mem T hx, LinearIsometry.norm_map]; rfl

theorem norm_polarIsometry_le (T : E →L[ℂ] F) : ‖T.polarIsometry‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  simp only [polarIsometry, comp_apply, one_mul]
  rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

@[simp]
theorem polarIsometry_apply_starProjection (T : E →L[ℂ] F) (x : E) :
    T.polarIsometry (T.polarInitial.starProjection x) = T.polarIsometry x := by
  have hx : x = T.polarInitial.starProjection x + (x - T.polarInitial.starProjection x) := by
    abel
  conv_rhs => rw [hx, map_add]
  rw [polarIsometry_apply_of_mem_orthogonal T
    (T.polarInitial.sub_starProjection_mem_orthogonal x), add_zero]

/-- `V† V` is the orthogonal projection onto the initial space. -/
theorem adjoint_polarIsometry_comp_polarIsometry_apply (T : E →L[ℂ] F) (x : E) :
    adjoint T.polarIsometry (T.polarIsometry x) = T.polarInitial.starProjection x := by
  set K := T.polarInitial
  refine ext_inner_left ℂ fun y => ?_
  rw [adjoint_inner_right, ← polarIsometry_apply_starProjection T y,
    ← polarIsometry_apply_starProjection T x,
    polarIsometry_apply_of_mem T (K.starProjection_apply_mem y),
    polarIsometry_apply_of_mem T (K.starProjection_apply_mem x), LinearIsometry.inner_map_map]
  change ⟪K.starProjection y, K.starProjection x⟫_ℂ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    K.starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]

/-- `V† T = |T|`. -/
@[simp]
theorem adjoint_polarIsometry_comp_self (T : E →L[ℂ] F) :
    adjoint T.polarIsometry ∘L T = T.polarAbs := by
  ext x
  rw [comp_apply, ← polarIsometry_polarAbs_apply T x,
    adjoint_polarIsometry_comp_polarIsometry_apply]
  exact T.polarInitial.starProjection_eq_self_iff.2 (polarAbs_apply_mem_polarInitial T x)

/-- **`ker V = ker T`.** -/
theorem ker_polarIsometry (T : E →L[ℂ] F) :
    LinearMap.ker (T.polarIsometry : E →ₗ[ℂ] F) = LinearMap.ker (T : E →ₗ[ℂ] F) := by
  rw [← polarInitial_orthogonal T]
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hx
    set K := T.polarInitial
    have h0 : K.starProjection x = 0 := by
      rw [← norm_eq_zero, ← norm_polarIsometry_apply_of_mem T (K.starProjection_apply_mem x),
        polarIsometry_apply_starProjection, hx, norm_zero]
    have := K.sub_starProjection_mem_orthogonal x
    rwa [h0, sub_zero] at this
  · exact polarIsometry_apply_of_mem_orthogonal T

/-- A partial isometry: `V V† V = V`. -/
def IsPartialIsometry (V : E →L[ℂ] F) : Prop := V ∘L adjoint V ∘L V = V

theorem IsPartialIsometry.adjoint_comp_self_idempotent {V : E →L[ℂ] F}
    (hV : IsPartialIsometry V) :
    (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L V := by
  have : (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L (V ∘L adjoint V ∘L V) := by
    simp only [comp_assoc]
  rw [this, hV]

theorem isPartialIsometry_polarIsometry (T : E →L[ℂ] F) :
    IsPartialIsometry T.polarIsometry := by
  ext x
  simp only [comp_apply]
  rw [adjoint_polarIsometry_comp_polarIsometry_apply, polarIsometry_apply_starProjection]

/-- **Uniqueness of the polar decomposition.** If `T = W A` with `A` positive, `W` isometric on
`range A` and zero on `(range A)ᗮ`, then `A = |T|` and `W = T.polarIsometry`. -/
theorem polar_unique {T : E →L[ℂ] F} {W : E →L[ℂ] F} {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hT : W ∘L A = T) (hWiso : ∀ x, ‖W (A x)‖ = ‖A x‖)
    (hW0 : ∀ x ∈ (LinearMap.range (A : E →ₗ[ℂ] E))ᗮ, W x = 0) :
    A = T.polarAbs ∧ W = T.polarIsometry := by
  have hAA : adjoint T ∘L T = A ∘L A := by
    have hz : ∀ x, ⟪(adjoint T ∘L T - A ∘L A) x, x⟫_ℂ = 0 := by
      intro x
      rw [sub_apply, inner_sub_left, comp_apply, adjoint_inner_left, comp_apply,
        ← adjoint_inner_right A, hA.isSelfAdjoint.adjoint_eq, ← hT, comp_apply,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hWiso, sub_self]
    have := (inner_map_self_eq_zero ((adjoint T ∘L T - A ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E)).1 hz
    exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective this)
  have hA' : A = T.polarAbs := by
    rw [polarAbs, hAA]
    exact (CFC.sqrt_mul_self A (nonneg_iff_isPositive.2 hA)).symm
  refine ⟨hA', ?_⟩
  subst hA'
  set K := T.polarInitial
  have hrange : LinearMap.range (T.polarAbs : E →ₗ[ℂ] E) ≤
      LinearMap.ker ((W - T.polarIsometry : E →L[ℂ] F) : E →ₗ[ℂ] F) := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply]
    rw [← comp_apply W, hT, polarIsometry_polarAbs_apply, sub_self]
  have hK : K ≤ LinearMap.ker ((W - T.polarIsometry : E →L[ℂ] F) : E →ₗ[ℂ] F) :=
    Submodule.topologicalClosure_minimal _ hrange (W - T.polarIsometry).isClosed_ker
  ext x
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  have horth : x - K.starProjection x ∈ (LinearMap.range (T.polarAbs : E →ₗ[ℂ] E))ᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure _)
      (K.sub_starProjection_mem_orthogonal x)
  have h1 := hK (K.starProjection_apply_mem x)
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, sub_eq_zero] at h1
  rw [hx, map_add, map_add, h1, hW0 _ horth,
    polarIsometry_apply_of_mem_orthogonal T (K.sub_starProjection_mem_orthogonal x)]

end ContinuousLinearMap
