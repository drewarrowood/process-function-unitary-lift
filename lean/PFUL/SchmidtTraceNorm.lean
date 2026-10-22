import PFUL.Schmidt

/-!
# The Schmidt series converges in trace norm

`tendsto_traceNorm_schmidt`: with `T x = ∑ₙ sₙ ⟪vₙ, x⟫ uₙ` as in `schmidt`, the finite partial
sums `T_F = ∑_{n ∈ F} sₙ |uₙ⟩⟨vₙ|` converge to `T` in trace norm, with
`‖T - T_F‖₁ ≤ ∑_{n ∉ F} sₙ`. `schmidt_traceNorm` packages this with `schmidt`.
-/

open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

universe u

namespace PFUL.TraceClass

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Classical in
theorem traceNorm_sub_schmidt_le {T : H →L[ℂ] H} (hT : T ∈ traceClass H) {ι : Type u}
    (v : HilbertBasis ι ℂ H) (u : ι → H) (s : ι → ℂ) (hs0 : ∀ n, 0 ≤ s n)
    (hTx : ∀ x, HasSum (fun n => (s n * ⟪v n, x⟫_ℂ) • u n) (T x))
    (hu : ∀ n m, s n ≠ 0 → s m ≠ 0 → ⟪u n, u m⟫_ℂ = if n = m then 1 else 0)
    {σ : ℝ} (hσ : HasSum (fun n => (s n).re) σ) (F : Finset ι) :
    traceNorm (T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n)) ≤
      ENNReal.ofReal (∑' n : {x // x ∉ F}, (s n).re) := by
  set R := T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n)
  have hR : R ∈ traceClass H :=
    sub_mem hT (sum_mem fun n _ => Submodule.smul_mem _ _ (rankOne_mem _ _))
  have hvv : ∀ n m, ⟪v n, v m⟫_ℂ = if n = m then 1 else 0 :=
    fun n m => orthonormal_iff_ite.1 v.orthonormal n m
  have hTv : ∀ m, T (v m) = s m • u m := by
    intro m
    have h1 := hTx (v m)
    have h2 : HasSum (fun n => (s n * ⟪v n, v m⟫_ℂ) • u n) ((s m * ⟪v m, v m⟫_ℂ) • u m) :=
      hasSum_single m fun n hn => by rw [hvv, ite_eq_right hn]; simp
    rw [h1.unique h2, hvv, ite_eq_left rfl, mul_one]
  have hRv : ∀ m, R (v m) = if m ∈ F then 0 else s m • u m := by
    intro m
    simp only [R, sub_apply, sum_apply, smul_apply, InnerProductSpace.rankOne_apply, hTv, hvv,
      ite_smul, one_smul, zero_smul, smul_ite, smul_zero]
    by_cases hm : m ∈ F <;> simp [hm]
  -- the bounding family
  set g : ι → ℝ := fun m => if m ∈ F then 0 else (s m).re
  have hg : HasSum g (∑' n : {x // x ∉ F}, (s n).re) := by
    have hsub : Summable fun n : {x // x ∉ F} => (s n).re := hσ.summable.subtype _
    have := (hasSum_subtype_iff_indicator (f := fun n => (s n).re) (s := {x | x ∉ F})).1 hsub.hasSum
    convert this using 1
    funext m; simp only [g, Set.indicator, Set.mem_ofPred_eq]; split_ifs <;> rfl
  refine iSup₂_le fun C hC => ?_
  have htr := hasSum_trace (comp_mem_left C hR) v
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (htr.norm_le_of_bounded hg fun m => ?_)
  simp only [comp_apply, hRv, g]
  split_ifs with hm
  · simp
  · have hre : ‖s m‖ = (s m).re := by
      obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 (hs0 m)
      rw [Complex.norm_eq_sqrt_sq_add_sq, ← h2]; simp [Real.sqrt_sq h1]
    by_cases hs : s m = 0
    · simp [hs]
    rw [map_smul, inner_smul_right, norm_mul, hre]
    have hum : ‖u m‖ = 1 := by
      have := hu m m hs hs
      rw [ite_eq_left rfl] at this
      have h' : ‖u m‖ ^ 2 = 1 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ), this]; simp
      nlinarith [norm_nonneg (u m), sq_nonneg (‖u m‖ - 1)]
    have : ‖⟪v m, C (u m)⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪v m, C (u m)⟫_ℂ‖ ≤ ‖v m‖ * ‖C (u m)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖C‖ * ‖u m‖) := by
          rw [v.orthonormal.1 m]; gcongr; exact C.le_opNorm _
        _ ≤ 1 := by rw [hum]; nlinarith [norm_nonneg C]
    nlinarith [(Complex.nonneg_iff.1 (hs0 m)).1]

open Classical in
/-- **Trace-norm convergence of the Schmidt series.** -/
theorem tendsto_traceNorm_schmidt {T : H →L[ℂ] H} (hT : T ∈ traceClass H) {ι : Type u}
    (v : HilbertBasis ι ℂ H) (u : ι → H) (s : ι → ℂ) (hs0 : ∀ n, 0 ≤ s n)
    (hTx : ∀ x, HasSum (fun n => (s n * ⟪v n, x⟫_ℂ) • u n) (T x))
    (hu : ∀ n m, s n ≠ 0 → s m ≠ 0 → ⟪u n, u m⟫_ℂ = if n = m then 1 else 0)
    {t : ℂ} (ht : HasSum s t) :
    Tendsto (fun F : Finset ι =>
      traceNorm (T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n))) atTop (𝓝 0) := by
  have hσ : HasSum (fun n => (s n).re) t.re := Complex.reCLM.hasSum ht
  have h0 := (tendsto_tsum_compl_atTop_zero fun n => (s n).re)
  have h1 : Tendsto (fun F : Finset ι => ENNReal.ofReal (∑' n : {x // x ∉ F}, (s n).re))
      atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    rw [ENNReal.ofReal_zero] at this; exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
    fun F => traceNorm_sub_schmidt_le hT v u s hs0 hTx hu hσ F

end PFUL.TraceClass

namespace PFUL.Polar
open PFUL.TraceClass

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Classical in
/-- **Schmidt decomposition, trace-norm form:** `T = ∑ₙ sₙ |uₙ⟩⟨vₙ|` in trace norm,
`∑ sₙ = Tr |T| = ‖T‖₁`. -/
theorem schmidt_traceNorm {T : H →L[ℂ] H} (hT : T ∈ traceClass H) :
    ∃ (ι : Type u) (v : HilbertBasis ι ℂ H) (u : ι → H) (s : ι → ℂ),
      (∀ n, 0 ≤ s n) ∧ (∀ n m, s n ≠ 0 → s m ≠ 0 → ⟪u n, u m⟫_ℂ = if n = m then 1 else 0) ∧
      HasSum s (trace (absOp T)) ∧ traceNorm T = ‖trace (absOp T)‖ₑ ∧
      Tendsto (fun F : Finset ι =>
        traceNorm (T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n))) atTop (𝓝 0) := by
  obtain ⟨ι, v, u, s, hs0, -, hTx, hu, hs, hn⟩ := schmidt hT
  exact ⟨ι, v, u, s, hs0, hu, hs, hn, tendsto_traceNorm_schmidt hT v u s hs0 hTx hu hs⟩

end PFUL.Polar
