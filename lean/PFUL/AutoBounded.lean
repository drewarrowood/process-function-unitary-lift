import PFUL.TraceNormDense

/-!
# Automatic trace-norm boundedness of positive trace-preserving maps (Round 16)

For a map `Φ` that is linear on the trace class, maps it into the trace class, preserves the
trace and sends positive trace-class operators to positive operators, we prove
`‖Φ T‖₁ ≤ 2 ‖T‖₁` for every trace-class `T` (and `‖Φ S‖₁ ≤ ‖S‖₁` for self-adjoint `S`).

Proof: Jordan decomposition `S = S⁺ - S⁻`, `S⁺ + S⁻ = |S|`, by the continuous functional calculus
(Mathlib's `CFC.posPart`, `CFC.negPart`, `CFC.posPart_add_negPart`); `‖P‖₁ = Tr P` for positive
`P` (from `traceNorm_eq_trace_abs`); and `T = Re T + i Im T`.

Consequence: the boundedness field of `IsNormalCPTP` is redundant: `IsCPTP Φ → IsNormalCPTP Φ`.
-/

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

universe u

namespace PFUL.TraceClass

open PFUL.Polar

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem trace_adjoint (A : H →L[ℂ] H) : trace (adjoint A) = star (trace A) := by
  simp only [trace]
  rw [tsum_star]
  congr 1; funext i
  rw [adjoint_inner_right, ← inner_conj_symm]
  rfl

theorem traceNorm_adjoint_le {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    traceNorm (adjoint T) ≤ traceNorm T := by
  refine iSup₂_le fun C hC => ?_
  have e : C ∘L adjoint T = adjoint (T ∘L adjoint C) := by
    rw [adjoint_comp, adjoint_adjoint]
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [← ofReal_norm, norm_star, ofReal_norm]
  rw [e, trace_adjoint, hs, ← trace_comp_comm _ hT]
  exact enorm_trace_comp_le (by rw [LinearIsometryEquiv.norm_map]; exact hC)

theorem traceNorm_smul_le (a : ℂ) (T : H →L[ℂ] H) :
    traceNorm (a • T) ≤ ‖a‖ₑ * traceNorm T := by
  refine iSup₂_le fun C hC => ?_
  rw [comp_smul, trace_smul', enorm_mul]
  gcongr
  exact enorm_trace_comp_le hC

theorem traceNorm_of_isPositive {T : H →L[ℂ] H} (hT : T ∈ traceClass H) (hp : T.IsPositive) :
    traceNorm T = ‖trace T‖ₑ := by
  rw [traceNorm_eq_trace_abs hT]
  congr 2
  exact CFC.abs_of_nonneg T (nonneg_iff_isPositive.2 hp)

theorem trace_of_isPositive {T : H →L[ℂ] H} (hT : T ∈ traceClass H) (hp : T.IsPositive) :
    ∃ r : ℝ, 0 ≤ r ∧ trace T = r := by
  obtain ⟨r, hr0, hr, -⟩ := trace_absOp_eq hT
  refine ⟨r, hr0, ?_⟩
  rw [← hr]
  congr 1
  exact (CFC.abs_of_nonneg T (nonneg_iff_isPositive.2 hp)).symm

/-- Positive, trace-preserving maps that are linear on the trace class. -/
structure IsPTP (Φ : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop where
  mem : ∀ T ∈ traceClass H, Φ T ∈ traceClass K
  map_add : ∀ S ∈ traceClass H, ∀ T ∈ traceClass H, Φ (S + T) = Φ S + Φ T
  map_smul : ∀ (a : ℂ), ∀ T ∈ traceClass H, Φ (a • T) = a • Φ T
  trace_eq : ∀ T ∈ traceClass H, trace (Φ T) = trace T
  pos : ∀ T ∈ traceClass H, T.IsPositive → (Φ T).IsPositive

theorem IsCPTP.toIsPTP {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsCPTP Φ) : IsPTP Φ where
  mem := h.mem
  map_add := h.map_add
  map_smul := h.map_smul
  trace_eq := h.trace_eq
  pos := fun _ hT hp => h.isPositive hT hp

/-- **Jordan decomposition** of a self-adjoint trace-class operator: `S⁺, S⁻` are positive,
trace class, `S = S⁺ - S⁻` and `S⁺ + S⁻ = |S|`. -/
theorem jordan {S : H →L[ℂ] H} (hS : S ∈ traceClass H) (hsa : IsSelfAdjoint S) :
    S⁺ ∈ traceClass H ∧ S⁻ ∈ traceClass H ∧ (S⁺).IsPositive ∧ (S⁻).IsPositive ∧
      S⁺ - S⁻ = S ∧ S⁺ + S⁻ = absOp S := by
  have h1 : S⁺ - S⁻ = S := CFC.posPart_sub_negPart S hsa
  have h2 : S⁺ + S⁻ = absOp S := CFC.posPart_add_negPart S hsa
  have hp : S⁺ = (1/2 : ℂ) • (absOp S + S) := by
    calc S⁺ = (1/2 : ℂ) • ((S⁺ + S⁻) + (S⁺ - S⁻)) := by module
      _ = _ := by rw [h1, h2]
  have hn : S⁻ = (1/2 : ℂ) • (absOp S - S) := by
    calc S⁻ = (1/2 : ℂ) • ((S⁺ + S⁻) - (S⁺ - S⁻)) := by module
      _ = _ := by rw [h1, h2]
  refine ⟨?_, ?_, nonneg_iff_isPositive.1 (CFC.posPart_nonneg S),
    nonneg_iff_isPositive.1 (CFC.negPart_nonneg S), h1, h2⟩
  · rw [hp]; exact Submodule.smul_mem _ _ (add_mem (absOp_mem hS) hS)
  · rw [hn]; exact Submodule.smul_mem _ _ (sub_mem (absOp_mem hS) hS)

theorem enorm_ofReal_add {p n : ℝ} (hp : 0 ≤ p) (hn : 0 ≤ n) :
    ‖(p : ℂ)‖ₑ + ‖(n : ℂ)‖ₑ = ‖((p : ℂ) + n)‖ₑ := by
  rw [← Complex.ofReal_add, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hp, Real.norm_of_nonneg hn,
    Real.norm_of_nonneg (add_nonneg hp hn), ENNReal.ofReal_add hp hn]

/-- **Self-adjoint inputs: `‖Φ S‖₁ ≤ ‖S‖₁`.** -/
theorem IsPTP.traceNorm_le_selfAdjoint {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsPTP Φ)
    {S : H →L[ℂ] H} (hS : S ∈ traceClass H) (hsa : IsSelfAdjoint S) :
    traceNorm (Φ S) ≤ traceNorm S := by
  obtain ⟨hP, hN, pP, pN, h1, h2⟩ := jordan hS hsa
  have eS : Φ S = Φ (S⁺) + (-1 : ℂ) • Φ (S⁻) := by
    rw [← h.map_smul _ _ hN, ← h.map_add _ hP _ (Submodule.smul_mem _ _ hN)]
    congr 1
    conv_lhs => rw [← h1]
    module
  obtain ⟨p, hp0, hpt⟩ := trace_of_isPositive hP pP
  obtain ⟨n, hn0, hnt⟩ := trace_of_isPositive hN pN
  calc traceNorm (Φ S) ≤ traceNorm (Φ (S⁺)) + traceNorm ((-1 : ℂ) • Φ (S⁻)) := by
        rw [eS]; exact traceNorm_add_le (h.mem _ hP) (Submodule.smul_mem _ _ (h.mem _ hN))
    _ ≤ traceNorm (Φ (S⁺)) + traceNorm (Φ (S⁻)) := by
        gcongr
        refine (traceNorm_smul_le _ _).trans ?_
        simp
    _ = ‖trace (S⁺)‖ₑ + ‖trace (S⁻)‖ₑ := by
        rw [traceNorm_of_isPositive (h.mem _ hP) (h.pos _ hP pP),
          traceNorm_of_isPositive (h.mem _ hN) (h.pos _ hN pN), h.trace_eq _ hP, h.trace_eq _ hN]
    _ = traceNorm S := by
        rw [traceNorm_eq_trace_abs hS, ← h2, trace_add hP hN, hpt, hnt, enorm_ofReal_add hp0 hn0]

/-- **Automatic boundedness: `‖Φ T‖₁ ≤ 2 ‖T‖₁`** for every positive trace-preserving map that is
linear on the trace class. -/
theorem IsPTP.traceNorm_le {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsPTP Φ)
    {T : H →L[ℂ] H} (hT : T ∈ traceClass H) : traceNorm (Φ T) ≤ 2 * traceNorm T := by
  set R : H →L[ℂ] H := (1/2 : ℂ) • (T + adjoint T) with hR
  set J : H →L[ℂ] H := (-(Complex.I / 2)) • (T - adjoint T) with hJ
  have hTa := adjoint_mem hT
  have hRm : R ∈ traceClass H := Submodule.smul_mem _ _ (add_mem hT hTa)
  have hJm : J ∈ traceClass H := Submodule.smul_mem _ _ (sub_mem hT hTa)
  have hRsa : IsSelfAdjoint R := by
    rw [IsSelfAdjoint, hR, star_smul, star_add, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint]
    rw [show star (1/2 : ℂ) = 1/2 by simp]
    rw [add_comm]
  have hJsa : IsSelfAdjoint J := by
    rw [IsSelfAdjoint, hJ, star_smul, star_sub, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint]
    rw [show star (-(Complex.I / 2)) = Complex.I / 2 by simp; ring]
    module
  have eT : T = R + Complex.I • J := by
    rw [hR, hJ]
    rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1/2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]; ring
    rw [this]; module
  have bR : traceNorm R ≤ traceNorm T := by
    calc traceNorm R ≤ ‖(1/2 : ℂ)‖ₑ * traceNorm (T + adjoint T) := traceNorm_smul_le _ _
      _ ≤ ‖(1/2 : ℂ)‖ₑ * (traceNorm T + traceNorm T) := by
          gcongr
          exact (traceNorm_add_le hT hTa).trans (add_le_add le_rfl (traceNorm_adjoint_le hT))
      _ = traceNorm T := by
          rw [← two_mul, ← mul_assoc]
          have : ‖(1/2 : ℂ)‖ₑ * 2 = 1 := by
            rw [← ofReal_norm]; norm_num
            rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            norm_num
          rw [this, one_mul]
  have bJ : traceNorm J ≤ traceNorm T := by
    calc traceNorm J ≤ ‖(-(Complex.I / 2))‖ₑ * traceNorm (T - adjoint T) := traceNorm_smul_le _ _
      _ ≤ ‖(-(Complex.I / 2))‖ₑ * (traceNorm T + traceNorm T) := by
          gcongr
          rw [sub_eq_add_neg, ← neg_one_smul ℂ (adjoint T)]
          refine (traceNorm_add_le hT (Submodule.smul_mem _ _ hTa)).trans
            (add_le_add le_rfl ((traceNorm_smul_le _ _).trans ?_))
          simpa using traceNorm_adjoint_le hT
      _ = traceNorm T := by
          rw [← two_mul, ← mul_assoc]
          have : ‖(-(Complex.I / 2))‖ₑ * 2 = 1 := by
            rw [← ofReal_norm]; norm_num
            rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            norm_num
          rw [this, one_mul]
  calc traceNorm (Φ T) = traceNorm (Φ R + Complex.I • Φ J) := by
        rw [eT, h.map_add _ hRm _ (Submodule.smul_mem _ _ hJm), h.map_smul _ _ hJm]
    _ ≤ traceNorm (Φ R) + traceNorm (Complex.I • Φ J) :=
        traceNorm_add_le (h.mem _ hRm) (Submodule.smul_mem _ _ (h.mem _ hJm))
    _ ≤ traceNorm R + traceNorm J := by
        gcongr
        · exact h.traceNorm_le_selfAdjoint hRm hRsa
        · refine (traceNorm_smul_le _ _).trans ?_
          rw [show ‖Complex.I‖ₑ = 1 by rw [← ofReal_norm]; simp, one_mul]
          exact h.traceNorm_le_selfAdjoint hJm hJsa
    _ ≤ traceNorm T + traceNorm T := add_le_add bR bJ
    _ = 2 * traceNorm T := (two_mul _).symm

/-- **The Round 8/9 gap, closed: every CPTP map on the trace class is normal (trace-norm
bounded).** The `bounded` field of `IsNormalCPTP` follows from the others. -/
theorem IsCPTP.isNormalCPTP {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsCPTP Φ) : IsNormalCPTP Φ where
  toIsCPTP := h
  bounded := ⟨2, fun _ hT => by
    simpa using h.toIsPTP.traceNorm_le hT⟩

theorem isNormalCPTP_iff {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} : IsNormalCPTP Φ ↔ IsCPTP Φ :=
  ⟨fun h => h.toIsCPTP, IsCPTP.isNormalCPTP⟩

end PFUL.TraceClass
