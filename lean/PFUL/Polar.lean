import PFUL.TraceClass
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Polar decomposition of bounded operators, and `‖T‖₁ = Tr |T|`

For every bounded `T` on a complex Hilbert space, `|T| = √(T†T)` (Mathlib's `CFC.abs` in the
C*-algebra `H →L[ℂ] H`) and a partial isometry `V` with `T = V |T|`, `V` isometric on
`closure (range |T|)` and zero on its orthogonal complement.
-/

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder

set_option linter.unusedSectionVars false

universe u

namespace PFUL.Polar

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `|T| = √(T† T)`. -/
noncomputable abbrev absOp (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.abs T

theorem absOp_isPositive (T : H →L[ℂ] H) : (absOp T).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.1 (CFC.abs_nonneg T)

theorem absOp_mul_self (T : H →L[ℂ] H) : absOp T ∘L absOp T = adjoint T ∘L T := by
  have := CFC.abs_mul_abs T
  rwa [ContinuousLinearMap.star_eq_adjoint] at this

theorem adjoint_absOp (T : H →L[ℂ] H) : adjoint (absOp T) = absOp T :=
  (absOp_isPositive T).isSelfAdjoint.adjoint_eq

theorem inner_absOp_absOp (T : H →L[ℂ] H) (x y : H) :
    ⟪absOp T x, absOp T y⟫_ℂ = ⟪T x, T y⟫_ℂ := by
  rw [← adjoint_inner_left, adjoint_absOp, ← comp_apply, absOp_mul_self, comp_apply,
    adjoint_inner_left]

/-- `‖ |T| x ‖ = ‖T x‖`. -/
theorem norm_absOp_apply (T : H →L[ℂ] H) (x : H) : ‖absOp T x‖ = ‖T x‖ := by
  have h := inner_absOp_absOp T x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖absOp T x‖ ^ 2 = ‖T x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

/-- The initial space `closure (range |T|)`. -/
noncomputable def initSp (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (absOp T : H →ₗ[ℂ] H)).topologicalClosure

instance (T : H →L[ℂ] H) : (initSp T).HasOrthogonalProjection := by
  have : CompleteSpace (initSp T) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- `x ↦ |T| x` as a map into the initial space. -/
noncomputable def toInit (T : H →L[ℂ] H) : H →ₗ[ℂ] initSp T :=
  LinearMap.codRestrict (initSp T) (absOp T : H →ₗ[ℂ] H)
    (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

theorem toInit_dense (T : H →L[ℂ] H) : DenseRange (toInit T) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro y
  have hy : (y : H) ∈ closure (Set.range (absOp T)) := by
    have := y.2
    change (y : H) ∈ ((LinearMap.range (absOp T : H →ₗ[ℂ] H)).topologicalClosure : Set H) at this
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at this
  convert hy using 2
  ext z; constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The isometry `closure (range |T|) → H`, `|T| x ↦ T x`. -/
noncomputable def isoPart (T : H →L[ℂ] H) : initSp T →ₗᵢ[ℂ] H :=
  (T : H →ₗ[ℂ] H).extendOfIsometry (toInit_dense T)
    (fun x => (norm_absOp_apply T x).symm)

theorem isoPart_toInit (T : H →L[ℂ] H) (x : H) : isoPart T (toInit T x) = T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- **The partial isometry** `V = W ∘ P`, with `P` the orthogonal projection onto the initial space. -/
noncomputable def partialIso (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (isoPart T).toContinuousLinearMap ∘L (initSp T).orthogonalProjectionOnto

/-- **Polar decomposition:** `T = V |T|`. -/
theorem polar (T : H →L[ℂ] H) : partialIso T ∘L absOp T = T := by
  ext x
  simp only [partialIso, comp_apply]
  have : (initSp T).orthogonalProjectionOnto (absOp T x) = toInit T x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (toInit T x)
  rw [this]; exact isoPart_toInit T x

theorem partialIso_of_mem (T : H →L[ℂ] H) {x : H} (hx : x ∈ initSp T) :
    partialIso T x = isoPart T ⟨x, hx⟩ := by
  simp only [partialIso, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ : initSp T)]; rfl

theorem partialIso_of_mem_orthogonal (T : H →L[ℂ] H) {x : H} (hx : x ∈ (initSp T)ᗮ) :
    partialIso T x = 0 := by
  simp only [partialIso, comp_apply]
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx]; simp

/-- `V` is isometric on the initial space. -/
theorem norm_partialIso_of_mem (T : H →L[ℂ] H) {x : H} (hx : x ∈ initSp T) :
    ‖partialIso T x‖ = ‖x‖ := by
  rw [partialIso_of_mem T hx, LinearIsometry.norm_map]; rfl

/-- `V† V = P` (the orthogonal projection onto the initial space). -/
theorem adjoint_partialIso_comp (T : H →L[ℂ] H) (x : H) :
    adjoint (partialIso T) (partialIso T x) = (initSp T).starProjection x := by
  set K := initSp T
  have hV : ∀ y, partialIso T y = partialIso T (K.starProjection y) := by
    intro y
    have hy : y = K.starProjection y + (y - K.starProjection y) := by abel
    conv_lhs => rw [hy, map_add]
    rw [partialIso_of_mem_orthogonal T (K.sub_starProjection_mem_orthogonal y), add_zero]
  refine ext_inner_left ℂ fun y => ?_
  rw [adjoint_inner_right, hV y, hV x, partialIso_of_mem T (K.starProjection_apply_mem y),
    partialIso_of_mem T (K.starProjection_apply_mem x), LinearIsometry.inner_map_map]
  change ⟪K.starProjection y, K.starProjection x⟫_ℂ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    K.starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]


theorem norm_partialIso_le (T : H →L[ℂ] H) : ‖partialIso T‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  simp only [partialIso, comp_apply, one_mul]
  rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

/-- `V† T = |T|`. -/
theorem adjoint_partialIso_comp_self (T : H →L[ℂ] H) : adjoint (partialIso T) ∘L T = absOp T := by
  ext x
  have h : T x = partialIso T (absOp T x) := by rw [← comp_apply, polar]
  rw [comp_apply, h, adjoint_partialIso_comp]
  exact (initSp T).starProjection_eq_self_iff.2
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (absOp T : H →ₗ[ℂ] H) x))

open PFUL.TraceClass

/-- `|T|` is trace class when `T` is. -/
theorem absOp_mem {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : absOp T ∈ traceClass H := by
  rw [← adjoint_partialIso_comp_self]; exact comp_mem_left _ hT

theorem two_mul_le_sq_add_sq (a b : ENNReal) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  rw [← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add,
    show (2 : ENNReal) = ((2 : NNReal) : ENNReal) from rfl, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/-- `√|T|`. -/
noncomputable abbrev sqrtAbs (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (absOp T)

theorem sqrtAbs_mul_self (T : H →L[ℂ] H) : sqrtAbs T ∘L sqrtAbs T = absOp T :=
  CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)

theorem adjoint_sqrtAbs (T : H →L[ℂ] H) : adjoint (sqrtAbs T) = sqrtAbs T :=
  (nonneg_iff_isPositive.1 (CFC.sqrt_nonneg (absOp T))).isSelfAdjoint.adjoint_eq

/-- `‖Tr |T|‖ = ‖√|T|‖₂²`, and `Tr |T|` is a nonnegative real. -/
theorem trace_absOp_eq {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    ∃ r : ℝ, 0 ≤ r ∧ trace (absOp T) = r ∧ ENNReal.ofReal r = hsSq (stdBasis H) (sqrtAbs T) := by
  set S := sqrtAbs T
  set e := stdBasis H
  have h := hasSum_trace (absOp_mem hT) e
  have hterm : ∀ i, ⟪e i, absOp T (e i)⟫_ℂ = ((‖S (e i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← sqrtAbs_mul_self, comp_apply, ← adjoint_inner_left, adjoint_sqrtAbs,
      inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [hterm] at h
  have hs : Summable fun i => ‖S (e i)‖ ^ 2 := Complex.summable_ofReal.1 h.summable
  refine ⟨∑' i, ‖S (e i)‖ ^ 2, tsum_nonneg fun i => by positivity,
    h.unique (Complex.hasSum_ofReal.2 hs.hasSum), ?_⟩
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs, hsSq]
  congr 1; funext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Trace norm = `Tr |T|`.** For trace-class `T`, the dual-norm definition
`‖T‖₁ = sup_{‖C‖≤1} |Tr(CT)|` equals `Tr |T|` (a nonnegative real). -/
theorem traceNorm_eq_trace_abs {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    traceNorm T = ‖trace (absOp T)‖ₑ := by
  obtain ⟨r, hr0, hr, hrS⟩ := trace_absOp_eq hT
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    set S := sqrtAbs T
    set V := partialIso T
    set e := stdBasis H
    set A := S ∘L adjoint (C ∘L V)
    have hCT : C ∘L T = adjoint A ∘L S := by
      rw [adjoint_comp, adjoint_adjoint, adjoint_sqrtAbs, comp_assoc, sqrtAbs_mul_self,
        comp_assoc, polar]
    have hSfin : hsSq e S ≠ ⊤ := by rw [← hrS]; exact ENNReal.ofReal_ne_top
    have hA : hsSq e A ≤ hsSq e S := by
      rw [hsSq_eq_adjoint e e, adjoint_comp, adjoint_adjoint, adjoint_sqrtAbs]
      refine (hsSq_comp_le _ _ _).trans ?_
      have : ‖C ∘L V‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          ((opNorm_comp_le _ _).trans (by simpa using mul_le_mul hC (norm_partialIso_le T) (norm_nonneg _) zero_le_one))
      calc _ ≤ 1 ^ 2 * hsSq e S := by gcongr
        _ = _ := by simp
    rw [hCT, trace_eq_tsum (hCT ▸ comp_mem_left C hT) e]
    simp only [comp_apply, adjoint_inner_right]
    have key : 2 * ∑' i, ‖⟪A (e i), S (e i)⟫_ℂ‖ₑ ≤ 2 * hsSq e S := by
      rw [← ENNReal.tsum_mul_left]
      calc ∑' i, 2 * ‖⟪A (e i), S (e i)⟫_ℂ‖ₑ
          ≤ ∑' i, (‖A (e i)‖ₑ ^ 2 + ‖S (e i)‖ₑ ^ 2) :=
            ENNReal.tsum_le_tsum fun i =>
              (by gcongr; exact enorm_inner_le _ _ : 2 * ‖⟪A (e i), S (e i)⟫_ℂ‖ₑ ≤ 2 * (‖A (e i)‖ₑ * ‖S (e i)‖ₑ)).trans (two_mul_le_sq_add_sq _ _)
        _ = hsSq e A + hsSq e S := ENNReal.tsum_add
        _ ≤ hsSq e S + hsSq e S := add_le_add hA le_rfl
        _ = 2 * hsSq e S := (two_mul _).symm
    have h2 : (2 : ENNReal)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    have key' : ∑' i, ‖⟪A (e i), S (e i)⟫_ℂ‖ₑ ≤ hsSq e S := by
      calc _ = (2 : ENNReal)⁻¹ * (2 * ∑' i, ‖⟪A (e i), S (e i)⟫_ℂ‖ₑ) := by
              rw [← mul_assoc, h2, one_mul]
        _ ≤ 2⁻¹ * (2 * hsSq e S) := by gcongr
        _ = _ := by rw [← mul_assoc, h2, one_mul]
    refine enorm_tsum_le_tsum_enorm.trans (key'.trans ?_)
    rw [← hrS, hr, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr0]
  · have h := enorm_trace_comp_le (T := T) (C := adjoint (partialIso T))
      (by rw [LinearIsometryEquiv.norm_map]; exact norm_partialIso_le T)
    rwa [adjoint_partialIso_comp_self] at h


/-! ## Partial isometries and uniqueness of the polar decomposition -/

/-- A partial isometry: `V V† V = V` (equivalently `V†V` is an orthogonal projection). -/
def IsPartialIsometry (V : H →L[ℂ] H) : Prop := V ∘L adjoint V ∘L V = V

theorem partialIso_eq_comp_proj (T : H →L[ℂ] H) (x : H) :
    partialIso T x = partialIso T ((initSp T).starProjection x) := by
  have hx : x = (initSp T).starProjection x + (x - (initSp T).starProjection x) := by abel
  conv_lhs => rw [hx, map_add]
  rw [partialIso_of_mem_orthogonal T ((initSp T).sub_starProjection_mem_orthogonal x), add_zero]

theorem isPartialIsometry_partialIso (T : H →L[ℂ] H) : IsPartialIsometry (partialIso T) := by
  ext x
  simp only [comp_apply]
  rw [adjoint_partialIso_comp, ← partialIso_eq_comp_proj]

/-- For a partial isometry, `V†V` is idempotent and self-adjoint (an orthogonal projection). -/
theorem IsPartialIsometry.proj {V : H →L[ℂ] H} (hV : IsPartialIsometry V) :
    (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L V ∧
      adjoint (adjoint V ∘L V) = adjoint V ∘L V := by
  refine ⟨?_, by rw [adjoint_comp, adjoint_adjoint]⟩
  have : (adjoint V ∘L V) ∘L (adjoint V ∘L V) = adjoint V ∘L (V ∘L adjoint V ∘L V) := by
    simp only [comp_assoc]
  rw [this, hV]

/-- **Uniqueness of the polar decomposition.** If `T = W A` with `A` positive, `W` isometric on
`range A` and zero on `(range A)ᗮ`, then `A = |T|` and `W` is the partial isometry `partialIso T`. -/
theorem polar_unique {T W A : H →L[ℂ] H} (hA : A.IsPositive) (hT : W ∘L A = T)
    (hWiso : ∀ x, ‖W (A x)‖ = ‖A x‖)
    (hW0 : ∀ x ∈ (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ, W x = 0) :
    A = absOp T ∧ W = partialIso T := by
  have hAA : adjoint T ∘L T = A ∘L A := by
    have hz : ∀ x, ⟪(adjoint T ∘L T - A ∘L A) x, x⟫_ℂ = 0 := by
      intro x
      rw [sub_apply, inner_sub_left, comp_apply, adjoint_inner_left, comp_apply,
        ← adjoint_inner_right A, hA.isSelfAdjoint.adjoint_eq, ← hT, comp_apply,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hWiso, sub_self]
    have := (inner_map_self_eq_zero ((adjoint T ∘L T - A ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 hz
    exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective this)
  have hA' : A = absOp T := by
    have h0 : 0 ≤ A := nonneg_iff_isPositive.2 hA
    change A = CFC.sqrt (star T * T)
    rw [ContinuousLinearMap.star_eq_adjoint]
    change A = CFC.sqrt (adjoint T ∘L T)
    rw [hAA]
    exact (CFC.sqrt_mul_self A h0).symm
  refine ⟨hA', ?_⟩
  subst hA'
  set K := initSp T
  have hrange : LinearMap.range (absOp T : H →ₗ[ℂ] H) ≤ LinearMap.ker ((W - partialIso T : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply]
    rw [← comp_apply W, hT, ← comp_apply (partialIso T), polar, sub_self]
  have hK : K ≤ LinearMap.ker ((W - partialIso T : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hrange (W - partialIso T).isClosed_ker
  ext x
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  have horth : x - K.starProjection x ∈ (LinearMap.range (absOp T : H →ₗ[ℂ] H))ᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure _) (K.sub_starProjection_mem_orthogonal x)
  have h1 := hK (K.starProjection_apply_mem x)
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, sub_eq_zero] at h1
  rw [hx, map_add, map_add, h1, hW0 _ horth,
    partialIso_of_mem_orthogonal T (K.sub_starProjection_mem_orthogonal x)]

/-- **Converse:** if `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` converges (in some Hilbert basis), `T` is trace class; so
`T ∈ traceClass ↔ Tr |T| < ∞`. -/
theorem mem_traceClass_iff {T : H →L[ℂ] H} {ι : Type u} (b : HilbertBasis ι ℂ H) :
    T ∈ traceClass H ↔ Summable fun i => (⟪b i, absOp T (b i)⟫_ℂ).re := by
  have hterm : ∀ i, (⟪b i, absOp T (b i)⟫_ℂ).re = ‖sqrtAbs T (b i)‖ ^ 2 := by
    intro i
    rw [← sqrtAbs_mul_self, comp_apply, ← adjoint_inner_left, adjoint_sqrtAbs,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  constructor
  · intro hT
    exact Complex.reCLM.summable (hasSum_trace (absOp_mem hT) b).summable
  · intro hs
    simp_rw [hterm] at hs
    have hS : IsHS (sqrtAbs T) := by
      refine IsHS.of_basis b ?_
      rw [hsSq]
      have : (fun i => ‖sqrtAbs T (b i)‖ₑ ^ 2) = fun i => ENNReal.ofReal (‖sqrtAbs T (b i)‖ ^ 2) := by
        funext i; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [this, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs]
      exact ENNReal.ofReal_ne_top
    have heq : T = adjoint (sqrtAbs T ∘L adjoint (partialIso T)) ∘L sqrtAbs T := by
      rw [adjoint_comp, adjoint_adjoint, adjoint_sqrtAbs, comp_assoc, sqrtAbs_mul_self, polar]
    rw [heq]
    exact Submodule.subset_span ⟨H, inferInstance, inferInstance, inferInstance, _, _,
      hS.comp_right _, hS, rfl⟩

end PFUL.Polar

#print axioms PFUL.Polar.polar
#print axioms PFUL.Polar.adjoint_partialIso_comp
#print axioms PFUL.Polar.traceNorm_eq_trace_abs
#print axioms PFUL.Polar.polar_unique
#print axioms PFUL.Polar.mem_traceClass_iff
#print axioms PFUL.Polar.isPartialIsometry_partialIso
