import PFUL.Polar

/-!
# Trace-class operators are compact; Schmidt decomposition

* `IsHS.isCompactOperator`: Hilbert–Schmidt operators are compact (norm limits of the finite-rank
  truncations `A ∘ P_F`, with `‖A - A P_F‖² ≤ ∑_{i ∉ F} ‖A eᵢ‖²`).
* `isCompactOperator_of_mem`: trace-class operators are compact.
* `schmidt`: for trace-class `T` there is a Hilbert basis `vₙ` of eigenvectors of `|T|`
  (from Mathlib's spectral theorem for compact self-adjoint operators,
  `orthogonalComplement_iSup_eigenspaces_eq_bot`) with eigenvalues `sₙ ≥ 0` such that
  `T x = ∑ₙ sₙ ⟪vₙ, x⟫ uₙ` (`uₙ = V vₙ`, orthonormal on `{sₙ ≠ 0}`), and `∑ₙ sₙ = Tr |T| = ‖T‖₁`.
-/

open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

universe u v

namespace PFUL.TraceClass

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isCompactOperator_rankOne (x : K) (y : H) :
    IsCompactOperator ((InnerProductSpace.rankOne ℂ x y : H →L[ℂ] K) : H → K) := by
  have : InnerProductSpace.rankOne ℂ x y = (ContinuousLinearMap.toSpanSingleton ℂ x : ℂ →L[ℂ] K) ∘L innerSL ℂ y := by
    ext z; simp [InnerProductSpace.rankOne_apply]
  rw [this, ContinuousLinearMap.coe_comp']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y : H →L[ℂ] ℂ)).clm_comp _

/-- Finite-rank truncation `A ∘ P_F`. -/
noncomputable def trunc {ι : Type*} (b : HilbertBasis ι ℂ H) (F : Finset ι) (A : H →L[ℂ] K) :
    H →L[ℂ] K :=
  ∑ i ∈ F, InnerProductSpace.rankOne ℂ (A (b i)) (b i)

theorem trunc_isCompact {ι : Type*} (b : HilbertBasis ι ℂ H) (F : Finset ι) (A : H →L[ℂ] K) :
    IsCompactOperator (trunc b F A) := by
  classical
  unfold trunc
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ContinuousLinearMap.coe_add']
    exact (isCompactOperator_rankOne _ _).add ih

theorem sub_trunc_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (F : Finset ι) (A : H →L[ℂ] K)
    (j : ι) [Decidable (j ∈ F)] : (A - trunc b F A) (b j) = if j ∈ F then 0 else A (b j) := by
  classical
  have ho := orthonormal_iff_ite.1 b.orthonormal
  simp only [trunc, sub_apply, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, ho]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
  split_ifs <;> simp

theorem norm_le_sqrt_hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) (C : H →L[ℂ] K)
    (h : hsSq b C ≠ ⊤) : ‖C‖ ≤ Real.sqrt (hsSq b C).toReal := by
  refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have h1 := enorm_apply_sq_le b C x
  have h2 : ‖C x‖ ^ 2 ≤ (hsSq b C).toReal * ‖x‖ ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top h (ENNReal.pow_ne_top enorm_ne_top)) h1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  rw [← Real.sqrt_sq (norm_nonneg (C x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul
    ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h2

/-- **Hilbert–Schmidt operators are compact.** -/
theorem IsHS.isCompactOperator {A : H →L[ℂ] K} (hA : IsHS A) : IsCompactOperator A := by
  classical
  set b := stdBasis H
  set f : _ → ℝ≥0∞ := fun i => ‖A (b i)‖ₑ ^ 2
  have hfin : ∑' i, f i ≠ ⊤ := hA.hsSq_ne_top b
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hfin
  have hhs : ∀ F : Finset _, hsSq b (A - trunc b F A) = ∑' i : {x // x ∉ F}, f i.1 := by
    intro F
    rw [hsSq]
    refine Eq.trans ?_ (tsum_subtype ({x | x ∉ F} : Set _) f).symm
    congr 1; funext j
    rw [sub_trunc_basis]
    by_cases hj : j ∈ F <;> simp [hj, Set.indicator, f]
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun F => trunc b F A) ?_
    (Eventually.of_forall fun F => trunc_isCompact b F A)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun F : Finset _ => Real.sqrt (∑' i : {x // x ∉ F}, f i.1).toReal) atTop
      (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) hlim
  rw [norm_sub_rev, ← hhs F]
  refine norm_le_sqrt_hsSq b _ ?_
  rw [hhs F]
  exact ne_top_of_le_ne_top hfin (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)

/-- **Trace-class operators are compact.** -/
theorem isCompactOperator_of_mem {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    IsCompactOperator T := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    rw [ContinuousLinearMap.coe_comp']
    exact hB.isCompactOperator.clm_comp (adjoint A)
  | zero => exact isCompactOperator_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.smul a

end PFUL.TraceClass

namespace PFUL.Polar
open PFUL.TraceClass

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isClosed_eigenspace (P : H →L[ℂ] H) (μ : ℂ) :
    IsClosed (Module.End.eigenspace (P : Module.End ℂ H) μ : Set H) := by
  have : (Module.End.eigenspace (P : Module.End ℂ H) μ : Set H) = {x : H | P x = μ • x} := by
    ext x; exact Module.End.mem_eigenspace_iff
  rw [this]; exact isClosed_eq P.continuous (continuous_id.const_smul μ)

instance (P : H →L[ℂ] H) (μ : ℂ) :
    CompleteSpace (Module.End.eigenspace (P : Module.End ℂ H) μ) :=
  (isClosed_eigenspace P μ).completeSpace_coe

/-- Index set of an eigenbasis of `|T|`. -/
abbrev EigIdx (T : H →L[ℂ] H) : Type u :=
  Σ μ : ℂ, (exists_hilbertBasis ℂ (Module.End.eigenspace (absOp T : Module.End ℂ H) μ)).choose

noncomputable def eigVec (T : H →L[ℂ] H) (n : EigIdx T) : H :=
  ((exists_hilbertBasis ℂ (Module.End.eigenspace (absOp T : Module.End ℂ H) n.1)).choose_spec.choose
    n.2 : H)

theorem eigVec_mem (T : H →L[ℂ] H) (n : EigIdx T) :
    absOp T (eigVec T n) = n.1 • eigVec T n :=
  Module.End.mem_eigenspace_iff.1 (Subtype.mem _)

theorem orthonormal_eigVec (T : H →L[ℂ] H) : Orthonormal ℂ (eigVec T) := by
  have hO := (absOp_isPositive T).isSymmetric.orthogonalFamily_eigenspaces
  exact hO.orthonormal_sigma_orthonormal (fun μ =>
    (exists_hilbertBasis ℂ (Module.End.eigenspace (absOp T : Module.End ℂ H) μ)).choose_spec.choose.orthonormal)

/-- **Eigenbasis of `|T|`** for trace-class (indeed compact) `T`. -/
noncomputable def eigBasis {T : H →L[ℂ] H} (hT : IsCompactOperator (absOp T)) :
    HilbertBasis (EigIdx T) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eigVec T) (by
    rw [eq_bot_iff]
    intro w hw
    have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT
      (absOp_isPositive T).isSymmetric
    rw [← hbot, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro μ
    rw [Submodule.mem_orthogonal']
    intro x hx
    set c := (exists_hilbertBasis ℂ (Module.End.eigenspace (absOp T : Module.End ℂ H) μ)).choose_spec.choose
    have hw' : ∀ j, ⟪w, (c j : H)⟫_ℂ = 0 := fun j =>
      (Submodule.mem_orthogonal' _ _).1 hw _ (Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩)
    have hsum := c.hasSum_repr ⟨x, hx⟩
    have hs2 := (hsum.mapL ((innerSL ℂ w).comp (Submodule.subtypeL _)))
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply,
      Submodule.coe_smul, inner_smul_right, hw', mul_zero] at hs2
    exact hs2.unique hasSum_zero)

theorem eigBasis_apply {T : H →L[ℂ] H} (hT : IsCompactOperator (absOp T)) (n : EigIdx T) :
    eigBasis hT n = eigVec T n := by
  rw [eigBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

open Classical in
/-- **Schmidt decomposition of a trace-class operator.** With `vₙ` the eigenbasis of `|T|`,
`sₙ = ⟪vₙ, |T| vₙ⟫ ≥ 0` (the singular values, with multiplicity) and `uₙ = V vₙ`:
`T x = ∑ₙ sₙ ⟪vₙ, x⟫ uₙ` for every `x`; the `uₙ` with `sₙ ≠ 0` are orthonormal; and
`∑ₙ sₙ = Tr |T|`, whose norm is the trace norm `‖T‖₁`. -/
theorem schmidt {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    ∃ (ι : Type u) (v : HilbertBasis ι ℂ H) (u : ι → H) (s : ι → ℂ),
      (∀ n, 0 ≤ s n) ∧ (∀ n, absOp T (v n) = s n • v n) ∧
      (∀ x, HasSum (fun n => (s n * ⟪v n, x⟫_ℂ) • u n) (T x)) ∧
      (∀ n m, s n ≠ 0 → s m ≠ 0 → ⟪u n, u m⟫_ℂ = if n = m then 1 else 0) ∧
      HasSum s (trace (absOp T)) ∧ traceNorm T = ‖trace (absOp T)‖ₑ := by
  have hc : IsCompactOperator (absOp T) := by
    rw [← adjoint_partialIso_comp_self, ContinuousLinearMap.coe_comp']
    exact (isCompactOperator_of_mem hT).clm_comp _
  set b := eigBasis hc
  set s : EigIdx T → ℂ := fun n => ⟪b n, absOp T (b n)⟫_ℂ
  have hev : ∀ n, absOp T (b n) = s n • b n := by
    intro n
    have h := eigVec_mem T n
    rw [← eigBasis_apply hc] at h
    have hs : s n = n.1 := by
      show ⟪b n, absOp T (b n)⟫_ℂ = n.1
      rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 n]; simp
    rw [h, hs]
  refine ⟨EigIdx T, b, fun n => partialIso T (b n), s, fun n => (absOp_isPositive T).inner_nonneg_right _,
    hev, fun x => ?_, fun n m hn hm => ?_, hasSum_trace (absOp_mem hT) b,
    traceNorm_eq_trace_abs hT⟩
  · have h1 := (b.hasSum_repr x).mapL (partialIso T ∘L absOp T)
    rw [polar] at h1
    convert h1 using 1
    funext n
    have hT' : T (b n) = s n • partialIso T (b n) := by
      have := congrArg (fun F => F (b n)) (polar T)
      simp only [comp_apply] at this
      rw [← this, hev, map_smul]
    simp only [map_smul, HilbertBasis.repr_apply_apply, hT', smul_smul]
    rw [mul_comm]
  · have hmem : ∀ k, s k ≠ 0 → (b k : H) ∈ initSp T := by
      intro k hk
      have : b k = absOp T ((s k)⁻¹ • b k) := by
        rw [map_smul, hev, smul_smul, inv_mul_cancel₀ hk, one_smul]
      rw [this]
      exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (absOp T : H →ₗ[ℂ] H) _)
    show ⟪partialIso T (b n), partialIso T (b m)⟫_ℂ = _
    rw [partialIso_of_mem T (hmem n hn), partialIso_of_mem T (hmem m hm),
      LinearIsometry.inner_map_map]
    convert orthonormal_iff_ite.1 b.orthonormal n m using 1
    · rfl
    · congr 1

end PFUL.Polar

#print axioms PFUL.TraceClass.isCompactOperator_of_mem
#print axioms PFUL.Polar.schmidt
