import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive

open scoped InnerProductSpace ENNReal NNReal
open ContinuousLinearMap
open scoped ComplexOrder

set_option linter.unusedSectionVars false

universe u v w

namespace PFUL.TraceClass

section HS
variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Parseval's identity for a Hilbert basis (real form). -/
theorem hasSum_norm_sq_inner {κ : Type*} (c : HilbertBasis κ ℂ K) (v : K) :
    HasSum (fun j => ‖⟪c j, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
  have h := (c.hasSum_inner_mul_inner v v).mapL Complex.reCLM
  have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.reCLM_apply, hv] at h
  convert h using 2 with j
  simp only [Complex.reCLM_apply]
  rw [← inner_conj_symm, Complex.mul_conj', RCLike.norm_conj]
  norm_cast

/-- Parseval's identity, `ℝ≥0∞` form. -/
theorem enorm_sq_eq_tsum {κ : Type*} (c : HilbertBasis κ ℂ K) (v : K) :
    ‖v‖ₑ ^ 2 = ∑' j, ‖⟪c j, v⟫_ℂ‖ₑ ^ 2 := by
  have h := hasSum_norm_sq_inner c v
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq]

/-- Squared Hilbert–Schmidt norm computed in a Hilbert basis. -/
noncomputable def hsSq {ι : Type*} (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] K) : ℝ≥0∞ :=
  ∑' i, ‖A (b i)‖ₑ ^ 2

theorem enorm_inner_symm (x y : H) : ‖⟪x, y⟫_ℂ‖ₑ = ‖⟪y, x⟫_ℂ‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]

/-- `‖A‖₂² = ‖A†‖₂²`, computed in arbitrary bases of the two spaces. -/
theorem hsSq_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (A : H →L[ℂ] K) : hsSq b A = hsSq c (adjoint A) := by
  unfold hsSq
  simp_rw [enorm_sq_eq_tsum c, enorm_sq_eq_tsum b (adjoint A _)]
  rw [ENNReal.tsum_comm]
  congr 1; funext j; congr 1; funext i
  rw [← adjoint_inner_left, enorm_inner_symm]

/-- The Hilbert–Schmidt norm does not depend on the basis. -/
theorem hsSq_indep {ι ι' : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis ι' ℂ H)
    (A : H →L[ℂ] K) : hsSq b A = hsSq b' A := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ K
  rw [hsSq_eq_adjoint b c, hsSq_eq_adjoint b' c]

/-- Hilbert–Schmidt operators: finite `∑ ‖A eᵢ‖²` (in every, equivalently some, Hilbert basis). -/
def IsHS (A : H →L[ℂ] K) : Prop := ∀ (ι : Type u) (b : HilbertBasis ι ℂ H), hsSq b A ≠ ⊤

theorem IsHS.of_basis {ι : Type*} (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] K}
    (h : hsSq b A ≠ ⊤) : IsHS A := fun _ b' => by rwa [hsSq_indep b' b]

theorem IsHS.hsSq_ne_top {A : H →L[ℂ] K} (h : IsHS A) {ι : Type*} (b : HilbertBasis ι ℂ H) :
    hsSq b A ≠ ⊤ := by
  obtain ⟨w, b0, -⟩ := exists_hilbertBasis ℂ H
  rw [hsSq_indep b b0]; exact h _ b0

theorem IsHS.adjoint {A : H →L[ℂ] K} (h : IsHS A) : IsHS (adjoint A) := by
  obtain ⟨w, b0, -⟩ := exists_hilbertBasis ℂ H
  intro ι c; rw [← hsSq_eq_adjoint b0 c]; exact h _ b0

theorem isHS_adjoint_iff {A : H →L[ℂ] K} : IsHS (adjoint A) ↔ IsHS A :=
  ⟨fun h => by simpa using IsHS.adjoint h, IsHS.adjoint⟩

theorem enorm_inner_le (x y : H) : ‖⟪x, y⟫_ℂ‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)

theorem enorm_apply_le (C : H →L[ℂ] K) (x : H) : ‖C x‖ₑ ≤ ‖C‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (C.le_opNorm x)

/-- The operator norm is dominated by the Hilbert–Schmidt norm. -/
theorem enorm_apply_sq_le {ι : Type*} (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] K) (x : H) :
    ‖A x‖ₑ ^ 2 ≤ hsSq b A * ‖x‖ₑ ^ 2 := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ K
  rw [hsSq_eq_adjoint b c, hsSq, enorm_sq_eq_tsum c, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  rw [← adjoint_inner_left, ← mul_pow]
  exact pow_le_pow_left₀ bot_le (enorm_inner_le _ _) 2

variable {H' : Type w} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem hsSq_comp_le {ι : Type*} (b : HilbertBasis ι ℂ H) (C : K →L[ℂ] H') (A : H →L[ℂ] K) :
    hsSq b (C ∘L A) ≤ ‖C‖ₑ ^ 2 * hsSq b A := by
  rw [hsSq, hsSq, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  rw [← mul_pow]
  exact pow_le_pow_left₀ bot_le (enorm_apply_le C _) 2

theorem IsHS.comp_left {A : H →L[ℂ] K} (h : IsHS A) (C : K →L[ℂ] H') : IsHS (C ∘L A) := by
  intro ι b
  refine ne_top_of_le_ne_top ?_ (hsSq_comp_le b C A)
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) (h _ b)

theorem IsHS.comp_right {A : H →L[ℂ] K} (h : IsHS A) (C : H' →L[ℂ] H) : IsHS (A ∘L C) := by
  rw [← isHS_adjoint_iff, adjoint_comp]
  exact IsHS.comp_left (IsHS.adjoint h) _

theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

/-- Double series `∑ᵢⱼ ‖⟪cⱼ, A bᵢ⟫‖²` equals `‖A‖₂²`. -/
theorem tsum_prod_enorm_sq {ι κ : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (A : H →L[ℂ] K) : ∑' p : ι × κ, ‖⟪c p.2, A (b p.1)⟫_ℂ‖ₑ ^ 2 = hsSq b A := by
  rw [ENNReal.tsum_prod', hsSq]
  simp_rw [enorm_sq_eq_tsum c (A _)]

/-- **Key lemma.** For Hilbert–Schmidt `A B : H → K`, `∑ᵢ ⟪A bᵢ, B bᵢ⟫` converges (unconditionally)
to `∑ⱼ ⟪B† cⱼ, A† cⱼ⟫`, for any Hilbert bases `b` of `H` and `c` of `K`. -/
theorem hasSum_inner_hs {ι κ : Type*} (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {A B : H →L[ℂ] K} (hA : hsSq b A ≠ ⊤) (hB : hsSq b B ≠ ⊤) :
    HasSum (fun i => ⟪A (b i), B (b i)⟫_ℂ) (∑' j, ⟪adjoint B (c j), adjoint A (c j)⟫_ℂ) := by
  let f : ι × κ → ℂ := fun p => ⟪A (b p.1), c p.2⟫_ℂ * ⟪c p.2, B (b p.1)⟫_ℂ
  have hfle : ∀ p, ‖f p‖ₑ ≤ ‖⟪c p.2, A (b p.1)⟫_ℂ‖ₑ ^ 2 + ‖⟪c p.2, B (b p.1)⟫_ℂ‖ₑ ^ 2 := by
    intro p
    simp only [f, enorm_mul]
    rw [enorm_inner_symm (A _)]
    exact mul_le_sq_add_sq _ _
  have hsum : Summable f := by
    refine Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hfle)
    rw [ENNReal.tsum_add, tsum_prod_enorm_sq, tsum_prod_enorm_sq]
    exact ENNReal.add_ne_top.2 ⟨hA, hB⟩
  have h1 : HasSum (fun i => ⟪A (b i), B (b i)⟫_ℂ) (∑' p, f p) :=
    hsum.hasSum.prod_fiberwise (fun i => c.hasSum_inner_mul_inner (A (b i)) (B (b i)))
  have hsum' : Summable (f ∘ Prod.swap) := (Equiv.prodComm κ ι).summable_iff.2 hsum
  have h2 : HasSum (fun j => ⟪adjoint B (c j), adjoint A (c j)⟫_ℂ) (∑' p, f p) := by
    rw [← (Equiv.prodComm κ ι).tsum_eq]
    refine hsum'.hasSum.prod_fiberwise (fun j => ?_)
    convert b.hasSum_inner_mul_inner (adjoint B (c j)) (adjoint A (c j)) using 1
    funext i
    simp only [Function.comp_apply, Prod.swap_prod_mk, f]
    rw [adjoint_inner_right, adjoint_inner_left, mul_comm]
  rw [h2.tsum_eq]; exact h1

end HS
section TC
open scoped ComplexOrder
variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generators of the trace class: products `A† B` of two Hilbert–Schmidt maps into some Hilbert
space `K`. -/
def gens : Set (H →L[ℂ] H) :=
  {T | ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
    (A B : H →L[ℂ] K), IsHS A ∧ IsHS B ∧ T = adjoint A ∘L B}

/-- **Trace-class operators**: the linear span of products of two Hilbert–Schmidt operators. (This is
the usual trace class `𝒮₁(H)`; it equals `{T | ∑ ⟪eᵢ, |T| eᵢ⟫ < ∞}` by the polar decomposition, which
is not formalised here.) -/
def traceClass : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ (gens H)

/-- A fixed Hilbert basis of `H`, used to define the trace. -/
noncomputable def stdBasis : HilbertBasis (exists_hilbertBasis ℂ H).choose ℂ H :=
  (exists_hilbertBasis ℂ H).choose_spec.choose

variable {H}

/-- The trace `Tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` (in the fixed basis; basis independence: `hasSum_trace`). -/
noncomputable def trace (T : H →L[ℂ] H) : ℂ := ∑' i, ⟪stdBasis H i, T (stdBasis H i)⟫_ℂ

theorem exists_hasSum {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : ∃ t : ℂ,
    ∀ (ι : Type u) (b : HilbertBasis ι ℂ H), HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) t := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ K
    refine ⟨∑' j, ⟪adjoint B (c j), adjoint A (c j)⟫_ℂ, fun ι b => ?_⟩
    have := hasSum_inner_hs b c (hA.hsSq_ne_top b) (hB.hsSq_ne_top b)
    simpa only [comp_apply, adjoint_inner_right] using this
  | zero => exact ⟨0, fun _ _ => by simpa using hasSum_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨t₁, h₁⟩ := hx; obtain ⟨t₂, h₂⟩ := hy
    exact ⟨t₁ + t₂, fun ι b => by simpa [inner_add_right] using (h₁ ι b).add (h₂ ι b)⟩
  | smul a x _ hx =>
    obtain ⟨t, h⟩ := hx
    exact ⟨a * t, fun ι b => by simpa [inner_smul_right] using (h ι b).mul_left a⟩

/-- **Summability and basis independence of the trace.** For trace-class `T` and *any* Hilbert basis
`b`, `∑ᵢ ⟪bᵢ, T bᵢ⟫` converges unconditionally to `trace T`. -/
theorem hasSum_trace {T : H →L[ℂ] H} (hT : T ∈ traceClass H) {ι : Type u}
    (b : HilbertBasis ι ℂ H) : HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T) := by
  obtain ⟨t, h⟩ := exists_hasSum hT
  rw [show trace T = t from (h _ (stdBasis H)).tsum_eq]
  exact h ι b

theorem trace_eq_tsum {T : H →L[ℂ] H} (hT : T ∈ traceClass H) {ι : Type u}
    (b : HilbertBasis ι ℂ H) : trace T = ∑' i, ⟪b i, T (b i)⟫_ℂ := (hasSum_trace hT b).tsum_eq.symm

theorem trace_add {S T : H →L[ℂ] H} (hS : S ∈ traceClass H) (hT : T ∈ traceClass H) :
    trace (S + T) = trace S + trace T := by
  have := (hasSum_trace hS (stdBasis H)).add (hasSum_trace hT (stdBasis H))
  simp only [← inner_add_right] at this
  exact this.tsum_eq

theorem trace_smul (a : ℂ) {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    trace (a • T) = a * trace T := by
  have := (hasSum_trace hT (stdBasis H)).mul_left a
  simp only [← inner_smul_right] at this
  exact this.tsum_eq

theorem trace_zero : trace (0 : H →L[ℂ] H) = 0 := by simp [trace]

/-- The trace as a linear functional on the trace class. -/
noncomputable def traceL : traceClass H →ₗ[ℂ] ℂ where
  toFun T := trace (T : H →L[ℂ] H)
  map_add' S T := trace_add S.2 T.2
  map_smul' a T := trace_smul a T.2

theorem adjoint_comp_mem {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A B : H →L[ℂ] K} (hA : IsHS A) (hB : IsHS B) : adjoint A ∘L B ∈ traceClass H :=
  Submodule.subset_span ⟨K, _, _, _, A, B, hA, hB, rfl⟩

/-- `Tr(A† B) = Tr(B A†)` for Hilbert–Schmidt `A, B : H → K`. -/
theorem trace_adjoint_comp_comm {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {A B : H →L[ℂ] K} (hA : IsHS A) (hB : IsHS B) :
    trace (adjoint A ∘L B) = trace (B ∘L adjoint A) := by
  have h := hasSum_inner_hs (stdBasis H) (stdBasis K) (hA.hsSq_ne_top (stdBasis H))
    (hB.hsSq_ne_top (stdBasis H))
  rw [trace, trace]
  simp only [comp_apply, adjoint_inner_right] at h ⊢
  rw [h.tsum_eq]
  congr 1; funext j; rw [← adjoint_inner_right, adjoint_inner_left]

/-- **Ideal property (left).** -/
theorem comp_mem_left (C : H →L[ℂ] H) {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    C ∘L T ∈ traceClass H := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    have : C ∘L (adjoint A ∘L B) = adjoint (A ∘L adjoint C) ∘L B := by
      rw [adjoint_comp, adjoint_adjoint, comp_assoc]
    rw [this]; exact adjoint_comp_mem (hA.comp_right _) hB
  | zero => simp
  | add x y _ _ hx hy => rw [comp_add]; exact add_mem hx hy
  | smul a x _ hx => rw [comp_smul]; exact Submodule.smul_mem _ a hx

/-- **Ideal property (right).** -/
theorem comp_mem_right (C : H →L[ℂ] H) {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    T ∘L C ∈ traceClass H := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    rw [comp_assoc]; exact adjoint_comp_mem hA (hB.comp_right _)
  | zero => simp
  | add x y _ _ hx hy => rw [add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comp]; exact Submodule.smul_mem _ a hx

theorem adjoint_mem {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : adjoint T ∈ traceClass H := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    rw [adjoint_comp, adjoint_adjoint]; exact adjoint_comp_mem hB hA
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- **Cyclicity:** `Tr(C T) = Tr(T C)` for trace-class `T` and bounded `C`. -/
theorem trace_comp_comm (C : H →L[ℂ] H) {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    trace (C ∘L T) = trace (T ∘L C) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    have e1 : C ∘L (adjoint A ∘L B) = adjoint (A ∘L adjoint C) ∘L B := by
      rw [adjoint_comp, adjoint_adjoint, comp_assoc]
    rw [e1, trace_adjoint_comp_comm (hA.comp_right _) hB, comp_assoc,
      trace_adjoint_comp_comm hA (hB.comp_right _), adjoint_comp, adjoint_adjoint, comp_assoc]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [comp_add, add_comp, trace_add (comp_mem_left C hx) (comp_mem_left C hy),
      trace_add (comp_mem_right C hx) (comp_mem_right C hy), ihx, ihy]
  | smul a x hx ih =>
    rw [comp_smul, smul_comp, trace_smul a (comp_mem_left C hx),
      trace_smul a (comp_mem_right C hx), ih]

/-- **Positivity:** a positive trace-class operator has nonnegative trace. -/
theorem trace_nonneg {T : H →L[ℂ] H} (hT : T ∈ traceClass H) (hpos : T.IsPositive) :
    0 ≤ trace T :=
  (hasSum_trace hT (stdBasis H)).nonneg (fun i => hpos.inner_nonneg_right _)

theorem isHS_innerSL (y : H) : IsHS (innerSL ℂ y) := by
  refine IsHS.of_basis (stdBasis H) ?_
  rw [hsSq]
  simp_rw [innerSL_apply_apply, enorm_inner_symm y]
  rw [← enorm_sq_eq_tsum]; exact ENNReal.pow_ne_top enorm_ne_top

theorem isHS_rankOne (v x : H) : IsHS (InnerProductSpace.rankOne ℂ v x) := by
  refine IsHS.of_basis (stdBasis H) ?_
  rw [hsSq]
  simp_rw [InnerProductSpace.rankOne_apply, enorm_smul, mul_pow, enorm_inner_symm x]
  rw [ENNReal.tsum_mul_right, ← enorm_sq_eq_tsum]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) (ENNReal.pow_ne_top enorm_ne_top)

theorem rankOne_mem (x y : H) : InnerProductSpace.rankOne ℂ x y ∈ traceClass H := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · rw [show InnerProductSpace.rankOne ℂ x y = 0 from Subsingleton.elim _ _]
    exact Submodule.zero_mem _
  obtain ⟨v, hv⟩ := exists_norm_eq H (zero_le_one : (0 : ℝ) ≤ 1)
  have : InnerProductSpace.rankOne ℂ x y =
      adjoint (InnerProductSpace.rankOne ℂ v x) ∘L InnerProductSpace.rankOne ℂ v y := by
    ext z
    rw [InnerProductSpace.adjoint_rankOne, comp_apply]
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [this]; exact adjoint_comp_mem (isHS_rankOne v x) (isHS_rankOne v y)

/-- **Trace of a rank-one operator:** `Tr |x⟩⟨y| = ⟪y, x⟫`. -/
theorem trace_rankOne (x y : H) : trace (InnerProductSpace.rankOne ℂ x y) = ⟪y, x⟫_ℂ := by
  rw [trace]
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  exact (stdBasis H).tsum_inner_mul_inner y x

/-- Trace norm, as the operator-norm dual: `‖T‖₁ = sup_{‖C‖ ≤ 1} |Tr (C T)|`. (For trace-class `T`
this is the usual `Tr |T|`; that identification is not formalised.) -/
noncomputable def traceNorm (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (C : H →L[ℂ] H) (_ : ‖C‖ ≤ 1), ‖trace (C ∘L T)‖ₑ

/-- `|Tr T| ≤ ‖T‖₁`. -/
theorem enorm_trace_le_traceNorm (T : H →L[ℂ] H) : ‖trace T‖ₑ ≤ traceNorm T :=
  le_iSup₂_of_le (ContinuousLinearMap.id ℂ H) (norm_id_le) (by simp)

theorem enorm_trace_comp_le {C T : H →L[ℂ] H} (hC : ‖C‖ ≤ 1) :
    ‖trace (C ∘L T)‖ₑ ≤ traceNorm T := le_iSup₂_of_le C hC le_rfl

/-- Bound for a generator, uniform in `‖C‖ ≤ 1`. -/
theorem enorm_trace_gen_le {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {A B : H →L[ℂ] K} (hA : IsHS A) (hB : IsHS B) {C : H →L[ℂ] H}
    (hC : ‖C‖ ≤ 1) :
    ‖trace (C ∘L (adjoint A ∘L B))‖ₑ ≤ hsSq (stdBasis K) (adjoint A) + hsSq (stdBasis H) B := by
  have e1 : C ∘L (adjoint A ∘L B) = adjoint (A ∘L adjoint C) ∘L B := by
    rw [adjoint_comp, adjoint_adjoint, comp_assoc]
  rw [e1, trace_eq_tsum (adjoint_comp_mem (hA.comp_right _) hB) (stdBasis H)]
  refine enorm_tsum_le_tsum_enorm.trans ?_
  simp only [comp_apply, adjoint_inner_right]
  calc ∑' i, ‖⟪(A ∘L adjoint C) (stdBasis H i), B (stdBasis H i)⟫_ℂ‖ₑ
      ≤ ∑' i, (‖(A ∘L adjoint C) (stdBasis H i)‖ₑ ^ 2 + ‖B (stdBasis H i)‖ₑ ^ 2) :=
        ENNReal.tsum_le_tsum (fun i => (enorm_inner_le _ _).trans (mul_le_sq_add_sq _ _))
    _ = hsSq (stdBasis H) (A ∘L adjoint C) + hsSq (stdBasis H) B := ENNReal.tsum_add
    _ ≤ _ := by
        gcongr
        rw [hsSq_eq_adjoint (stdBasis H) (stdBasis K), adjoint_comp, adjoint_adjoint]
        refine (hsSq_comp_le _ _ _).trans ?_
        have : ‖C‖ₑ ≤ 1 := by
          rw [← ofReal_norm, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC
        calc ‖C‖ₑ ^ 2 * hsSq (stdBasis K) (adjoint A) ≤ 1 ^ 2 * hsSq (stdBasis K) (adjoint A) := by
              gcongr
          _ = _ := by simp

/-- The trace norm of a trace-class operator is finite. -/
theorem traceNorm_ne_top {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : traceNorm T ≠ ⊤ := by
  suffices h : ∃ M ≠ ⊤, ∀ C : H →L[ℂ] H, ‖C‖ ≤ 1 → ‖trace (C ∘L T)‖ₑ ≤ M by
    obtain ⟨M, hM, h⟩ := h
    exact ne_top_of_le_ne_top hM (iSup₂_le h)
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    exact ⟨_, ENNReal.add_ne_top.2 ⟨hA.adjoint.hsSq_ne_top _, hB.hsSq_ne_top _⟩,
      fun C hC => enorm_trace_gen_le hA hB hC⟩
  | zero => exact ⟨0, ENNReal.zero_ne_top, fun C _ => by simp [trace_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨M₁, h₁, k₁⟩ := ihx; obtain ⟨M₂, h₂, k₂⟩ := ihy
    refine ⟨M₁ + M₂, ENNReal.add_ne_top.2 ⟨h₁, h₂⟩, fun C hC => ?_⟩
    rw [comp_add, trace_add (comp_mem_left C hx) (comp_mem_left C hy)]
    exact (enorm_add_le _ _).trans (add_le_add (k₁ C hC) (k₂ C hC))
  | smul a x hx ih =>
    obtain ⟨M, hM, k⟩ := ih
    refine ⟨‖a‖ₑ * M, ENNReal.mul_ne_top enorm_ne_top hM, fun C hC => ?_⟩
    rw [comp_smul, trace_smul a (comp_mem_left C hx), enorm_mul]
    gcongr; exact k C hC

/-- Triangle inequality for the trace norm. -/
theorem traceNorm_add_le {S T : H →L[ℂ] H} (hS : S ∈ traceClass H) (hT : T ∈ traceClass H) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  refine iSup₂_le (fun C hC => ?_)
  rw [comp_add, trace_add (comp_mem_left C hS) (comp_mem_left C hT)]
  exact (enorm_add_le _ _).trans (add_le_add (enorm_trace_comp_le hC) (enorm_trace_comp_le hC))

/-- Two trace-class operators with the same `Tr(· C)` for all bounded `C` are equal
(it suffices to test against rank-one `C`; no trace-class hypothesis is needed). -/
theorem eq_of_trace_comp {P Q : H →L[ℂ] H}
    (h : ∀ C : H →L[ℂ] H, trace (P ∘L C) = trace (Q ∘L C)) : P = Q := by
  refine ext fun y => ext_inner_left ℂ fun x => ?_
  have := h (InnerProductSpace.rankOne ℂ y x)
  rwa [InnerProductSpace.comp_rankOne, InnerProductSpace.comp_rankOne, trace_rankOne,
    trace_rankOne] at this

end TC

section L2
variable {J : Type u} {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem lp_enorm_sq (f : lp (fun _ : J => K) 2) : ‖f‖ₑ ^ 2 = ∑' j, ‖f j‖ₑ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq]

theorem memℓp_of_enorm {g : J → K} (h : ∑' j, ‖g j‖ₑ ^ 2 ≠ ⊤) : Memℓp g 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have : Summable (fun j => ‖g j‖₊ ^ 2) :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using h)
  have := NNReal.summable_coe.2 this
  simpa using this

theorem norm_le_of_enorm_sq_le {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {y : Y} {x : X} {M : ℝ≥0∞} (hM : M ≠ ⊤) (h : ‖y‖ₑ ^ 2 ≤ M * ‖x‖ₑ ^ 2) :
    ‖y‖ ≤ √M.toReal * ‖x‖ := by
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hM (ENNReal.pow_ne_top enorm_ne_top)) h
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul, toReal_enorm] at h2
  rw [← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h2

end L2

section Conj
variable {H H' : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- Conjugation `T ↦ U T U†` maps the trace class of `H` into that of `H'`. -/
theorem conj_mem (U : H →L[ℂ] H') {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    U ∘L T ∘L adjoint U ∈ traceClass H' := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    have : U ∘L (adjoint A ∘L B) ∘L adjoint U = adjoint (A ∘L adjoint U) ∘L (B ∘L adjoint U) := by
      rw [adjoint_comp, adjoint_adjoint]; simp only [comp_assoc]
    rw [this]; exact adjoint_comp_mem (hA.comp_right _) (hB.comp_right _)
  | zero => simp
  | add x y _ _ hx hy => rw [add_comp, comp_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comp, comp_smul]; exact Submodule.smul_mem _ a hx

/-- **Conjugation by an isometry preserves the trace:** `U†U = 1 ⇒ Tr(U T U†) = Tr T`. -/
theorem trace_conj (U : H →L[ℂ] H') (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ H)
    {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : trace (U ∘L T ∘L adjoint U) = trace T := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    have : U ∘L (adjoint A ∘L B) ∘L adjoint U = adjoint (A ∘L adjoint U) ∘L (B ∘L adjoint U) := by
      rw [adjoint_comp, adjoint_adjoint]; simp only [comp_assoc]
    rw [this, trace_adjoint_comp_comm (hA.comp_right _) (hB.comp_right _),
      trace_adjoint_comp_comm hA hB, adjoint_comp, adjoint_adjoint, comp_assoc,
      ← comp_assoc (adjoint U), hU, id_comp]
  | zero => simp [trace_zero]
  | add x y hx hy ihx ihy =>
    rw [add_comp, comp_add, trace_add (conj_mem U hx) (conj_mem U hy), trace_add hx hy, ihx, ihy]
  | smul a x hx ih =>
    rw [smul_comp, comp_smul, trace_smul a (conj_mem U hx), trace_smul a hx, ih]

end Conj

/-- Density operators: positive trace-class operators of unit trace. -/
def IsDensity {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : H →L[ℂ] H) : Prop :=
  ρ ∈ traceClass H ∧ ρ.IsPositive ∧ trace ρ = 1

theorem IsDensity.conj {H H' : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {ρ : H →L[ℂ] H} (h : IsDensity ρ) (U : H →L[ℂ] H')
    (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ H) : IsDensity (U ∘L ρ ∘L adjoint U) :=
  ⟨conj_mem U h.1, h.2.1.conj_adjoint U, by rw [trace_conj U hU h.1, h.2.2]⟩

/-! ## The tensor product `H ⊗ ℓ²(J)` as `ℓ²(J; H)`, and the partial trace over `J` -/

section PTrace
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {J : Type u} [DecidableEq J]
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `slot j : H → ℓ²(J; H)`, `x ↦ x ⊗ δⱼ`. -/
noncomputable def slot (j : J) : H →L[ℂ] lp (fun _ : J => H) 2 :=
  (lp.lsingle (E := fun _ : J => H) (𝕜 := ℂ) 2 j).mkContinuous 1
    (fun x => by simp [lp.norm_single (p := 2) (by norm_num)])

theorem slot_apply (j : J) (x : H) (j' : J) : slot j x j' = Pi.single (M := fun _ => H) j x j' :=
  lp.single_apply (E := fun _ : J => H) 2 j x j'

theorem inner_slot_left (j : J) (x : H) (f : lp (fun _ : J => H) 2) :
    ⟪slot j x, f⟫_ℂ = ⟪x, f j⟫_ℂ := lp.inner_single_left j x f

theorem amp_sum_le (C : H →L[ℂ] H) (f : lp (fun _ : J => H) 2) :
    ∑' j, ‖C (f j)‖ₑ ^ 2 ≤ ‖C‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
  rw [lp_enorm_sq, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  rw [← mul_pow]; exact pow_le_pow_left₀ bot_le (enorm_apply_le _ _) 2

/-- The amplification `C ⊗ 1` on `ℓ²(J; H) = H ⊗ ℓ²(J)`. -/
noncomputable def amp (C : H →L[ℂ] H) : lp (fun _ : J => H) 2 →L[ℂ] lp (fun _ : J => H) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun j => C (f j), memℓp_of_enorm (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) (ENNReal.pow_ne_top enorm_ne_top))
        (amp_sum_le C f))⟩
      map_add' := fun f g => lp.ext (funext fun j => by simp; rfl)
      map_smul' := fun a f => lp.ext (funext fun j => by simp [Pi.smul_apply]) }
    (√(‖C‖ₑ ^ 2).toReal)
    (fun f => norm_le_of_enorm_sq_le (ENNReal.pow_ne_top enorm_ne_top)
      (by rw [lp_enorm_sq]; exact amp_sum_le C f))

theorem amp_apply (C : H →L[ℂ] H) (f : lp (fun _ : J => H) 2) (j : J) :
    amp C f j = C (f j) := rfl

theorem amp_slot (C : H →L[ℂ] H) (j : J) (x : H) : amp C (slot j x) = slot j (C x) := by
  refine lp.ext (funext fun j' => ?_)
  change C (slot j x j') = slot j (C x) j'
  rw [slot_apply, slot_apply]
  by_cases h : j' = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem amp_id : amp (J := J) (ContinuousLinearMap.id ℂ H) = ContinuousLinearMap.id ℂ _ := by
  ext f : 1; exact lp.ext (funext fun j => rfl)

theorem orthonormal_slot {ι : Type*} (b : HilbertBasis ι ℂ H) :
    Orthonormal ℂ (fun p : J × ι => slot p.1 (b p.2)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨j, i⟩ ⟨j', i'⟩
  rw [inner_slot_left, slot_apply]
  by_cases h : j = j'
  · subst h
    simp only [Pi.single_eq_same, Prod.mk.injEq, true_and]
    exact (orthonormal_iff_ite.1 b.orthonormal) i i'
  · rw [Pi.single_eq_of_ne h, inner_zero_right]
    simp [h]

/-- The product Hilbert basis `(j, i) ↦ bᵢ ⊗ δⱼ` of `ℓ²(J; H)`. -/
noncomputable def prodBasis {ι : Type*} (b : HilbertBasis ι ℂ H) :
    HilbertBasis (J × ι) ℂ (lp (fun _ : J => H) 2) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_slot b) (by
    refine (Submodule.eq_bot_iff _).2 (fun f hf => ?_)
    have h0 : ∀ j i, ⟪b i, f j⟫_ℂ = 0 := fun j i => by
      rw [← inner_slot_left]
      exact (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨(j, i), rfl⟩)
    refine lp.ext (funext fun j => ?_)
    have : b.repr (f j) = 0 := lp.ext (funext fun i => by
      rw [b.repr_apply_apply, h0]; rfl)
    simpa using this)

theorem coe_prodBasis {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ⇑(prodBasis (J := J) b) = fun p : J × ι => slot p.1 (b p.2) :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

theorem hsSq_prodBasis {ι : Type*} (b : HilbertBasis ι ℂ H) (A : lp (fun _ : J => H) 2 →L[ℂ] K) :
    hsSq (prodBasis b) A = ∑' j, hsSq b (A ∘L slot j) := by
  rw [hsSq, coe_prodBasis, ENNReal.tsum_prod']; rfl

theorem lift_sum_le (A : lp (fun _ : J => H) 2 →L[ℂ] K) (x : H) :
    ∑' j, ‖A (slot j x)‖ₑ ^ 2 ≤ hsSq (prodBasis (stdBasis H)) A * ‖x‖ₑ ^ 2 := by
  rw [hsSq_prodBasis, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum (fun j => enorm_apply_sq_le (stdBasis H) (A ∘L slot j) x)

/-- For Hilbert–Schmidt `A : ℓ²(J; H) → K`, the map `H → ℓ²(J; K)`, `x ↦ (A (x ⊗ δⱼ))ⱼ`. -/
noncomputable def lift (A : lp (fun _ : J => H) 2 →L[ℂ] K) (hA : IsHS A) :
    H →L[ℂ] lp (fun _ : J => K) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => A (slot j x), memℓp_of_enorm (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (hA.hsSq_ne_top _) (ENNReal.pow_ne_top enorm_ne_top))
        (lift_sum_le A x))⟩
      map_add' := fun f g => lp.ext (funext fun j => by simp; rfl)
      map_smul' := fun a f => lp.ext (funext fun j => by simp [Pi.smul_apply]) }
    (√(hsSq (prodBasis (stdBasis H)) A).toReal)
    (fun x => norm_le_of_enorm_sq_le (hA.hsSq_ne_top _)
      (by rw [lp_enorm_sq]; exact lift_sum_le A x))

theorem lift_apply (A : lp (fun _ : J => H) 2 →L[ℂ] K) (hA : IsHS A) (x : H) (j : J) :
    lift A hA x j = A (slot j x) := rfl

theorem isHS_lift (A : lp (fun _ : J => H) 2 →L[ℂ] K) (hA : IsHS A) : IsHS (lift A hA) := by
  refine IsHS.of_basis (stdBasis H) ?_
  have : hsSq (stdBasis H) (lift A hA) = hsSq (prodBasis (stdBasis H)) A := by
    rw [hsSq_prodBasis, hsSq]
    simp_rw [lp_enorm_sq, lift_apply]
    rw [ENNReal.tsum_comm]; rfl
  rw [this]; exact hA.hsSq_ne_top _

/-- Partial trace of a generator `A† B`, characterised against `C ⊗ 1`. -/
theorem trace_lift_comp (A B : lp (fun _ : J => H) 2 →L[ℂ] K) (hA : IsHS A) (hB : IsHS B)
    (C : H →L[ℂ] H) :
    trace ((adjoint (lift A hA) ∘L lift B hB) ∘L C) = trace ((adjoint A ∘L B) ∘L amp C) := by
  set b := stdBasis H
  have h1 := hasSum_trace (comp_mem_right C (adjoint_comp_mem (isHS_lift A hA) (isHS_lift B hB))) b
  have h2 := hasSum_trace (comp_mem_right (amp C) (adjoint_comp_mem hA hB)) (prodBasis b)
  rw [coe_prodBasis] at h2
  simp only [comp_apply, adjoint_inner_right, amp_slot] at h1 h2
  have h3 := ((Equiv.prodComm _ _).hasSum_iff.2 h2).prod_fiberwise
    (fun i => (lp.summable_inner (lift A hA (b i)) (lift B hB (C (b i)))).hasSum)
  simp_rw [← lp.inner_eq_tsum] at h3
  exact h1.unique h3

theorem exists_ptrace {T : lp (fun _ : J => H) 2 →L[ℂ] lp (fun _ : J => H) 2}
    (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) :
    ∃ P ∈ traceClass H, ∀ C : H →L[ℂ] H, trace (P ∘L C) = trace (T ∘L amp C) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    exact ⟨_, adjoint_comp_mem (isHS_lift A hA) (isHS_lift B hB), trace_lift_comp A B hA hB⟩
  | zero => exact ⟨0, zero_mem _, fun C => by simp [trace_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨P₁, hP₁, k₁⟩ := ihx; obtain ⟨P₂, hP₂, k₂⟩ := ihy
    refine ⟨P₁ + P₂, add_mem hP₁ hP₂, fun C => ?_⟩
    rw [add_comp, add_comp, trace_add (comp_mem_right C hP₁) (comp_mem_right C hP₂),
      trace_add (comp_mem_right _ hx) (comp_mem_right _ hy), k₁, k₂]
  | smul a x hx ih =>
    obtain ⟨P, hP, k⟩ := ih
    refine ⟨a • P, Submodule.smul_mem _ a hP, fun C => ?_⟩
    rw [smul_comp, smul_comp, trace_smul a (comp_mem_right C hP),
      trace_smul a (comp_mem_right _ hx), k]

open Classical in
/-- **Partial trace** `Tr_J : 𝒮₁(H ⊗ ℓ²(J)) → 𝒮₁(H)` (zero off the trace class). -/
noncomputable def ptrace (T : lp (fun _ : J => H) 2 →L[ℂ] lp (fun _ : J => H) 2) : H →L[ℂ] H :=
  if h : T ∈ traceClass (lp (fun _ : J => H) 2) then (exists_ptrace h).choose else 0

variable {T S : lp (fun _ : J => H) 2 →L[ℂ] lp (fun _ : J => H) 2}

theorem ptrace_mem (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) : ptrace T ∈ traceClass H := by
  rw [ptrace, dite_eq_left hT]; exact (exists_ptrace hT).choose_spec.1

/-- **Defining property of the partial trace:** `Tr(Tr_J(T) C) = Tr(T (C ⊗ 1))`. -/
theorem trace_ptrace_comp (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) (C : H →L[ℂ] H) :
    trace (ptrace T ∘L C) = trace (T ∘L amp C) := by
  rw [ptrace, dite_eq_left hT]; exact (exists_ptrace hT).choose_spec.2 C

/-- **Uniqueness:** any operator with the defining property is the partial trace. -/
theorem ptrace_unique (P : H →L[ℂ] H)
    (hP : ∀ C : H →L[ℂ] H, trace (P ∘L C) = trace (T ∘L amp C))
    (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) : ptrace T = P :=
  eq_of_trace_comp (fun C => by rw [trace_ptrace_comp hT, hP])

theorem ptrace_add (hS : S ∈ traceClass (lp (fun _ : J => H) 2))
    (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) : ptrace (S + T) = ptrace S + ptrace T := by
  refine ptrace_unique _ (fun C => ?_) (add_mem hS hT)
  rw [add_comp, add_comp, trace_add (comp_mem_right C (ptrace_mem hS))
    (comp_mem_right C (ptrace_mem hT)), trace_add (comp_mem_right _ hS) (comp_mem_right _ hT),
    trace_ptrace_comp hS, trace_ptrace_comp hT]

theorem ptrace_smul (a : ℂ) (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) :
    ptrace (a • T) = a • ptrace T := by
  refine ptrace_unique _ (fun C => ?_) (Submodule.smul_mem _ a hT)
  rw [smul_comp, smul_comp, trace_smul a (comp_mem_right C (ptrace_mem hT)),
    trace_smul a (comp_mem_right _ hT), trace_ptrace_comp hT]

/-- **Trace preservation:** `Tr(Tr_J T) = Tr T`. -/
theorem trace_ptrace (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) :
    trace (ptrace T) = trace T := by
  have := trace_ptrace_comp hT (ContinuousLinearMap.id ℂ H)
  rwa [amp_id, comp_id, comp_id] at this

/-- Matrix elements of the partial trace: `⟪x, Tr_J(T) y⟫ = ∑ⱼ ⟪x ⊗ δⱼ, T (y ⊗ δⱼ)⟫`. -/
theorem hasSum_inner_ptrace (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) (x y : H) :
    HasSum (fun j => ⟪slot j x, T (slot j y)⟫_ℂ) ⟪x, ptrace T y⟫_ℂ := by
  set b := stdBasis H
  have key := trace_ptrace_comp hT (InnerProductSpace.rankOne ℂ y x)
  rw [InnerProductSpace.comp_rankOne, trace_rankOne] at key
  rw [key]
  have h2 := hasSum_trace (comp_mem_right (amp (InnerProductSpace.rankOne ℂ y x)) hT)
    (prodBasis b)
  rw [coe_prodBasis] at h2
  refine h2.prod_fiberwise (fun j => ?_)
  simp only [comp_apply, amp_slot, InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  have := b.hasSum_inner_mul_inner x (adjoint (slot j) (T (slot j y)))
  simp only [adjoint_inner_right, inner_slot_left] at this ⊢
  convert this using 1

/-- **Positivity preservation.** -/
theorem ptrace_isPositive (hT : T ∈ traceClass (lp (fun _ : J => H) 2)) (hpos : T.IsPositive) :
    (ptrace T).IsPositive := by
  rw [isPositive_iff_complex]
  intro x
  have h0 : 0 ≤ ⟪x, ptrace T x⟫_ℂ :=
    (hasSum_inner_ptrace hT x x).nonneg (fun j => hpos.inner_nonneg_right _)
  have hz : 0 ≤ ⟪ptrace T x, x⟫_ℂ := by
    rw [← inner_conj_symm]; exact star_nonneg_iff.2 h0
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hz
  exact ⟨Complex.ext (by simp) (by simpa using h2), h1⟩

theorem IsDensity.ptrace (h : IsDensity T) : IsDensity (ptrace T) :=
  ⟨ptrace_mem h.1, ptrace_isPositive h.1 h.2.1, by rw [trace_ptrace h.1, h.2.2]⟩

theorem inner_slot_right (j : J) (x : H) (f : lp (fun _ : J => H) 2) :
    ⟪f, slot j x⟫_ℂ = ⟪f j, x⟫_ℂ := by
  rw [← inner_conj_symm, inner_slot_left, inner_conj_symm]

/-- The elementary tensor `x ⊗ y ∈ ℓ²(J; H)`, `(x ⊗ y)ⱼ = yⱼ • x`. -/
noncomputable def tensor (x : H) (y : lp (fun _ : J => ℂ) 2) : lp (fun _ : J => H) 2 :=
  ⟨fun j => y j • x, memℓp_of_enorm (by
    simp_rw [enorm_smul, mul_pow]
    rw [ENNReal.tsum_mul_right, ← lp_enorm_sq]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) (ENNReal.pow_ne_top enorm_ne_top))⟩

theorem tensor_apply (x : H) (y : lp (fun _ : J => ℂ) 2) (j : J) : tensor x y j = y j • x := rfl

theorem amp_tensor (C : H →L[ℂ] H) (x : H) (y : lp (fun _ : J => ℂ) 2) :
    amp C (tensor x y) = tensor (C x) y :=
  lp.ext (funext fun j => by simp [amp_apply, tensor_apply])

theorem slot_eq_tensor (j : J) (x : H) : slot j x = tensor x (lp.single 2 j (1 : ℂ)) := by
  refine lp.ext (funext fun j' => ?_)
  change slot j x j' = (lp.single 2 j (1 : ℂ) : lp (fun _ : J => ℂ) 2) j' • x
  rw [slot_apply, lp.single_apply]
  by_cases h : j' = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem inner_tensor (x x' : H) (y y' : lp (fun _ : J => ℂ) 2) :
    ⟪tensor x y, tensor x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_mul_left]
  congr 1; funext j
  simp only [tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
  ring

/-- **Partial trace of a product operator:** `Tr_J |x ⊗ y⟩⟨x' ⊗ y'| = ⟪y', y⟫ |x⟩⟨x'|`. -/
theorem ptrace_rankOne_tensor (x x' : H) (y y' : lp (fun _ : J => ℂ) 2) :
    ptrace (InnerProductSpace.rankOne ℂ (tensor x y) (tensor x' y')) =
      ⟪y', y⟫_ℂ • InnerProductSpace.rankOne ℂ x x' := by
  have hT := rankOne_mem (tensor x y) (tensor x' y')
  refine ext fun v => ext_inner_left ℂ fun u => ?_
  refine (hasSum_inner_ptrace hT u v).unique ?_
  have h := ((lp.summable_inner y' y).hasSum).mul_left (⟪x', v⟫_ℂ * ⟪u, x⟫_ℂ)
  rw [← lp.inner_eq_tsum] at h
  convert h using 1
  · funext j
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, inner_slot_left,
      inner_slot_right, tensor_apply, inner_smul_left, lp.coeFn_smul, Pi.smul_apply,
      RCLike.inner_apply]
    ring
  · simp only [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_right, smul_eq_mul]
    ring

end PTrace

/-! ## `ℓ²(I × J) ≅ ℓ²(J; ℓ²(I))` and the partial trace on `ℓ²(I × J)` -/

section Prod
variable {I J : Type u} [DecidableEq I] [DecidableEq J]

/-- The product basis indexed by `I × J`. -/
noncomputable def prodBasisIJ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis I ℂ H) : HilbertBasis (I × J) ℂ (lp (fun _ : J => H) 2) :=
  HilbertBasis.mkOfOrthogonalEqBot ((orthonormal_slot (J := J) b).comp Prod.swap
    Prod.swap_injective) (by
      have : Set.range ((fun p : J × I => slot p.1 (b p.2)) ∘ Prod.swap) =
          Set.range (fun p : J × I => slot p.1 (b p.2)) :=
        Prod.swap_surjective.range_comp _
      rw [this, ← coe_prodBasis]
      exact Submodule.topologicalClosure_eq_top_iff.1 (prodBasis (J := J) b).dense_span)

/-- `ℓ²(I × J) ≃ ℓ²(J; ℓ²(I))`, `δ₍ᵢ,ⱼ₎ ↦ δᵢ ⊗ δⱼ`: the concrete tensor product
`ℓ²(I) ⊗ ℓ²(J) = ℓ²(I × J)`. -/
noncomputable def l2ProdEquiv (I J : Type u) [DecidableEq I] [DecidableEq J] :
    lp (fun _ : I × J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => lp (fun _ : I => ℂ) 2) 2 :=
  (prodBasisIJ (J := J) (default : HilbertBasis I ℂ (lp (fun _ : I => ℂ) 2))).repr.symm

theorem l2ProdEquiv_single (i : I) (j : J) :
    l2ProdEquiv I J (lp.single 2 (i, j) 1) = slot j (lp.single 2 i (1 : ℂ)) := by
  rw [l2ProdEquiv, HilbertBasis.repr_symm_single, prodBasisIJ, HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [Function.comp_apply, Prod.swap_prod_mk]
  congr 1
  rw [← HilbertBasis.repr_symm_single]; rfl

/-- `l2ProdEquiv` as a bounded operator. -/
noncomputable def l2ProdCLM (I J : Type u) [DecidableEq I] [DecidableEq J] :
    lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : J => lp (fun _ : I => ℂ) 2) 2 :=
  ((l2ProdEquiv I J : lp (fun _ : I × J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => lp (fun _ : I => ℂ) 2) 2) :
    lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : J => lp (fun _ : I => ℂ) 2) 2)

/-- Partial trace over `J` of an operator on `ℓ²(I × J)`. -/
noncomputable def ptraceR (T : lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : I × J => ℂ) 2) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  ptrace (l2ProdCLM I J ∘L T ∘L adjoint (l2ProdCLM I J))

theorem adjoint_comp_self_linearIsometryEquiv {E F : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (U : E ≃ₗᵢ[ℂ] F) :
    adjoint (U : E →L[ℂ] F) ∘L (U : E →L[ℂ] F) = ContinuousLinearMap.id ℂ E := by
  ext x; refine ext_inner_left ℂ fun y => ?_
  simp [adjoint_inner_right]

theorem IsDensity.ptraceR {T : lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : I × J => ℂ) 2}
    (h : IsDensity T) : IsDensity (ptraceR T) :=
  IsDensity.ptrace (h.conj (l2ProdCLM I J) (adjoint_comp_self_linearIsometryEquiv _))

/-- Defining property on `ℓ²(I × J)`: `Tr(Tr_J(T) C) = Tr(T (C ⊗ 1))`, with `C ⊗ 1` transported. -/
theorem trace_ptraceR_comp {T : lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : I × J => ℂ) 2}
    (hT : T ∈ traceClass _) (C : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    trace (ptraceR T ∘L C) = trace (T ∘L (adjoint (l2ProdCLM I J) ∘L amp C ∘L
      l2ProdCLM I J)) := by
  set U : lp (fun _ : I × J => ℂ) 2 →L[ℂ] _ := l2ProdCLM I J
  have hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ _ :=
    adjoint_comp_self_linearIsometryEquiv (l2ProdEquiv I J)
  have hadj : ∀ x, adjoint U x = (l2ProdEquiv I J).symm x := fun x =>
    ext_inner_left ℂ fun y => by
      rw [adjoint_inner_right]
      change ⟪l2ProdEquiv I J y, x⟫_ℂ = _
      conv_lhs => rw [← (l2ProdEquiv I J).apply_symm_apply x]
      exact (l2ProdEquiv I J).inner_map_map y _
  have hU' : U ∘L adjoint U = ContinuousLinearMap.id ℂ _ := ContinuousLinearMap.ext fun x => by
    rw [comp_apply, hadj]; exact (l2ProdEquiv I J).apply_symm_apply x
  rw [ptraceR, trace_ptrace_comp (conj_mem U hT)]
  have e : U ∘L T ∘L adjoint U ∘L amp C =
      U ∘L (T ∘L (adjoint U ∘L amp C ∘L U)) ∘L adjoint U := by
    simp only [comp_assoc, hU', comp_id]
  rw [show (U ∘L T ∘L adjoint U) ∘L amp C = U ∘L T ∘L adjoint U ∘L amp C by simp only [comp_assoc],
    e, trace_conj U hU (comp_mem_right _ hT)]

theorem trace_ptraceR {T : lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : I × J => ℂ) 2}
    (hT : T ∈ traceClass _) : trace (ptraceR T) = trace T := by
  rw [ptraceR, trace_ptrace (conj_mem _ hT),
    trace_conj (l2ProdCLM I J) (adjoint_comp_self_linearIsometryEquiv _) hT]

end Prod

end PFUL.TraceClass

#print axioms PFUL.TraceClass.hsSq_indep
#print axioms PFUL.TraceClass.hasSum_trace
#print axioms PFUL.TraceClass.traceL
#print axioms PFUL.TraceClass.trace_comp_comm
#print axioms PFUL.TraceClass.comp_mem_left
#print axioms PFUL.TraceClass.comp_mem_right
#print axioms PFUL.TraceClass.trace_nonneg
#print axioms PFUL.TraceClass.trace_rankOne
#print axioms PFUL.TraceClass.enorm_trace_le_traceNorm
#print axioms PFUL.TraceClass.traceNorm_ne_top
#print axioms PFUL.TraceClass.trace_conj
#print axioms PFUL.TraceClass.trace_ptrace_comp
#print axioms PFUL.TraceClass.ptrace_unique
#print axioms PFUL.TraceClass.ptrace_add
#print axioms PFUL.TraceClass.ptrace_smul
#print axioms PFUL.TraceClass.ptrace_isPositive
#print axioms PFUL.TraceClass.trace_ptrace
#print axioms PFUL.TraceClass.hasSum_inner_ptrace
#print axioms PFUL.TraceClass.ptrace_rankOne_tensor
#print axioms PFUL.TraceClass.trace_ptraceR_comp
#print axioms PFUL.TraceClass.IsDensity.ptraceR
