import PFUL.CPTP
import PFUL.SchmidtTraceNorm

/-!
# Trace-norm density of finite-rank operators; normal CPTP maps

* `exists_finiteRank_traceNorm_lt`: finite-rank operators are dense in the trace class for the
  trace norm (from the trace-norm Schmidt decomposition).
* `traceNorm_rankOne_le`, `enorm_inner_apply_le`, `traceNorm_ptrace_le`, `traceNorm_conj_le`.
* `IsNormalCPTP`: `IsCPTP` plus trace-norm boundedness (= continuity, for maps linear on the
  trace class). `isNormalCPTP_stinespring`: Stinespring/Kraus channels are normal CPTP.
* `eq_of_rankOne_basis`: two normal CPTP maps agreeing on the matrix units `|bᵢ⟩⟨bⱼ|` of a Hilbert
  basis agree on the whole trace class.
-/

open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

universe u

namespace PFUL.TraceClass

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem trace_smul' (a : ℂ) (T : H →L[ℂ] H) : trace (a • T) = a * trace T := by
  simp only [trace, smul_apply, inner_smul_right]; exact tsum_mul_left

theorem enorm_trace_comp_le' (C X : H →L[ℂ] H) :
    ‖trace (C ∘L X)‖ₑ ≤ ‖C‖ₑ * traceNorm X := by
  by_cases hC : C = 0
  · subst hC; simp [trace_zero]
  have hn : ‖C‖ ≠ 0 := norm_ne_zero_iff.2 hC
  set C' := ((‖C‖⁻¹ : ℝ) : ℂ) • C
  have hC' : ‖C'‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have e : C ∘L X = ((‖C‖ : ℝ) : ℂ) • (C' ∘L X) := by
    rw [smul_comp, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn]; simp
  rw [e, trace_smul', enorm_mul]
  gcongr
  · simp [enorm_eq_nnnorm]
  · exact enorm_trace_comp_le hC'

/-- `⟪z, X x⟫ = Tr(|x⟩⟨z| X)`. -/
theorem inner_eq_trace_comp (X : H →L[ℂ] H) (x z : H) :
    ⟪z, X x⟫_ℂ = trace (InnerProductSpace.rankOne ℂ x z ∘L X) := by
  rw [InnerProductSpace.rankOne_comp, trace_rankOne, ← adjoint_inner_left]

theorem enorm_inner_apply_le (X : H →L[ℂ] H) (x z : H) :
    ‖⟪z, X x⟫_ℂ‖ₑ ≤ ‖x‖ₑ * ‖z‖ₑ * traceNorm X := by
  rw [inner_eq_trace_comp]
  refine (enorm_trace_comp_le' _ _).trans ?_
  rw [InnerProductSpace.enorm_rankOne]

theorem traceNorm_rankOne_le (x y : H) :
    traceNorm (InnerProductSpace.rankOne ℂ x y) ≤ ‖x‖ₑ * ‖y‖ₑ := by
  refine iSup₂_le fun C hC => ?_
  rw [InnerProductSpace.comp_rankOne, trace_rankOne]
  calc ‖⟪y, C x⟫_ℂ‖ₑ ≤ ‖y‖ₑ * ‖C x‖ₑ := enorm_inner_le _ _
    _ ≤ ‖y‖ₑ * (‖C‖ₑ * ‖x‖ₑ) := by gcongr; exact enorm_apply_le _ _
    _ ≤ ‖y‖ₑ * (1 * ‖x‖ₑ) := by
        gcongr; rw [← ofReal_norm]; simpa using ENNReal.ofReal_le_ofReal hC
    _ = ‖x‖ₑ * ‖y‖ₑ := by ring

/-- **Finite-rank operators are trace-norm dense in the trace class.** -/
theorem exists_finiteRank_traceNorm_lt {T : H →L[ℂ] H} (hT : T ∈ traceClass H) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ (ι : Type u) (F : Finset ι) (x y : ι → H),
      traceNorm (T - ∑ n ∈ F, InnerProductSpace.rankOne ℂ (x n) (y n)) < ε := by
  obtain ⟨ι, v, u, s, -, -, -, -, ht⟩ := PFUL.Polar.schmidt_traceNorm hT
  obtain ⟨F, hF⟩ := (ht.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  refine ⟨ι, F, fun n => s n • u n, v, ?_⟩
  simpa [map_smul] using hF

/-! ### Trace-norm bounds for partial trace and conjugation -/

section PT
variable {J : Type u} [DecidableEq J]

theorem norm_amp_le (C : H →L[ℂ] H) : ‖amp (J := J) C‖ ≤ ‖C‖ := by
  refine LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _ |>.trans_eq ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.toReal_ofReal
    (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem traceNorm_ptrace_le {Y : lp (fun _ : J => H) 2 →L[ℂ] lp (fun _ : J => H) 2}
    (hY : Y ∈ traceClass _) : traceNorm (ptrace Y) ≤ traceNorm Y := by
  refine iSup₂_le fun C hC => ?_
  rw [trace_comp_comm C (ptrace_mem hY), trace_ptrace_comp hY, ← trace_comp_comm _ hY]
  exact enorm_trace_comp_le ((norm_amp_le C).trans hC)

end PT

variable {H' : Type u} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- Cyclicity across spaces: `Tr(C W T W†) = Tr(W† C W T)`. -/
theorem trace_conj_comp (W : H →L[ℂ] H') (C : H' →L[ℂ] H') {T : H →L[ℂ] H}
    (hT : T ∈ traceClass H) :
    trace (C ∘L (W ∘L T ∘L adjoint W)) = trace ((adjoint W ∘L C ∘L W) ∘L T) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A, B, hA, hB, rfl⟩ := hT
    have e1 : C ∘L (W ∘L (adjoint A ∘L B) ∘L adjoint W) =
        adjoint (A ∘L adjoint W ∘L adjoint C) ∘L (B ∘L adjoint W) := by
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
    have e2 : (adjoint W ∘L C ∘L W) ∘L (adjoint A ∘L B) =
        adjoint (A ∘L adjoint (adjoint W ∘L C ∘L W)) ∘L B := by
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
    rw [e1, e2, trace_adjoint_comp_comm (hA.comp_right _) (hB.comp_right _),
      trace_adjoint_comp_comm (hA.comp_right _) hB]
    congr 1
    simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
  | zero => simp [trace_zero]
  | add x y hx hy ihx ihy =>
    rw [add_comp, comp_add, comp_add, comp_add,
      trace_add (comp_mem_left C (conj_mem W hx)) (comp_mem_left C (conj_mem W hy)),
      trace_add (comp_mem_left _ hx) (comp_mem_left _ hy), ihx, ihy]
  | smul a x hx ih =>
    rw [smul_comp, comp_smul, comp_smul, comp_smul, trace_smul', trace_smul', ih]

theorem traceNorm_conj_le (W : H →L[ℂ] H') (hW : ‖W‖ ≤ 1) {T : H →L[ℂ] H}
    (hT : T ∈ traceClass H) : traceNorm (W ∘L T ∘L adjoint W) ≤ traceNorm T := by
  refine iSup₂_le fun C hC => ?_
  rw [trace_conj_comp W C hT]
  refine enorm_trace_comp_le ?_
  calc ‖adjoint W ∘L C ∘L W‖ ≤ ‖adjoint W‖ * (‖C‖ * ‖W‖) :=
        (opNorm_comp_le _ _).trans (by gcongr; exact opNorm_comp_le _ _)
    _ ≤ 1 * (1 * 1) := by
        rw [adjoint.norm_map]; gcongr
    _ = 1 := by norm_num

theorem norm_le_one_of_isometry (W : H →L[ℂ] H')
    (hW : adjoint W ∘L W = ContinuousLinearMap.id ℂ H) : ‖W‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  have h : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ← adjoint_inner_right, ← comp_apply, hW, id_apply]
  rw [one_mul]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h).le

/-! ### Normal CPTP maps -/

/-- Normal (trace-norm bounded, i.e. trace-norm continuous) CPTP maps on the trace class. -/
structure IsNormalCPTP (Φ : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop extends IsCPTP Φ where
  bounded : ∃ c : ℝ≥0, ∀ T ∈ traceClass H, traceNorm (Φ T) ≤ c * traceNorm T

theorem isNormalCPTP_stinespring {J : Type u} [DecidableEq J] (V : H →L[ℂ] lp (fun _ : J => K) 2)
    (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ H) : IsNormalCPTP (stinespring V) where
  toIsCPTP := isCPTP_stinespring V hV
  bounded := ⟨1, fun T hT => by
    rw [ENNReal.coe_one, one_mul]
    exact (traceNorm_ptrace_le (conj_mem V hT)).trans
      (traceNorm_conj_le V (norm_le_one_of_isometry V hV) hT)⟩

/-- A bounded (conjugate-)linear functional vanishing on a Hilbert basis vanishes. -/
theorem eq_zero_of_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (L : H → ℂ)
    (hadd : ∀ u v, L (u + v) = L u + L v) (hsmul : ∀ (a : ℂ) u, L (a • u) = a * L u)
    (M : ℝ) (hM : ∀ u, ‖L u‖ ≤ M * ‖u‖) (h0 : ∀ i, L (b i) = 0) : ∀ u, L u = 0 := by
  let L' : H →L[ℂ] ℂ := LinearMap.mkContinuous ⟨⟨L, hadd⟩, hsmul⟩ M hM
  have hker : Submodule.span ℂ (Set.range b) ≤ LinearMap.ker (L' : H →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h0 i)
  have hcl := Submodule.topologicalClosure_minimal _ hker (L'.isClosed_ker)
  rw [b.dense_span] at hcl
  intro u
  exact hcl (Submodule.mem_top (x := u))

/-- **Uniqueness from matrix units.** Two normal CPTP maps that agree on `|bᵢ⟩⟨bⱼ|` agree on the
trace class. -/
theorem eq_of_rankOne_basis {Φ Ψ : (H →L[ℂ] H) → (K →L[ℂ] K)} (hΦ : IsNormalCPTP Φ)
    (hΨ : IsNormalCPTP Ψ) {ι : Type*} (b : HilbertBasis ι ℂ H)
    (h : ∀ i j, Φ (InnerProductSpace.rankOne ℂ (b i) (b j)) =
      Ψ (InnerProductSpace.rankOne ℂ (b i) (b j))) :
    ∀ T ∈ traceClass H, Φ T = Ψ T := by
  obtain ⟨c, hc⟩ := hΦ.bounded
  obtain ⟨c', hc'⟩ := hΨ.bounded
  intro T hT
  refine ext fun x => ext_inner_left ℂ fun z => ?_
  rw [← sub_eq_zero]
  -- the functional `f`
  set f : (H →L[ℂ] H) → ℂ := fun S => ⟪z, Φ S x⟫_ℂ - ⟪z, Ψ S x⟫_ℂ with hf
  change f T = 0
  have fadd : ∀ S ∈ traceClass H, ∀ S' ∈ traceClass H, f (S + S') = f S + f S' := by
    intro S hS S' hS'
    simp only [hf, hΦ.map_add S hS S' hS', hΨ.map_add S hS S' hS', add_apply, inner_add_right]
    ring
  have fsmul : ∀ (a : ℂ), ∀ S ∈ traceClass H, f (a • S) = a * f S := by
    intro a S hS
    simp only [hf, hΦ.map_smul a S hS, hΨ.map_smul a S hS, smul_apply, inner_smul_right]
    ring
  set M : ℝ≥0∞ := ‖x‖ₑ * ‖z‖ₑ * ((c : ℝ≥0∞) + c')
  have hMtop : M ≠ ⊤ := by simp [M, ENNReal.mul_eq_top]
  have fbd : ∀ S ∈ traceClass H, ‖f S‖ₑ ≤ M * traceNorm S := by
    intro S hS
    calc ‖f S‖ₑ ≤ ‖⟪z, Φ S x⟫_ℂ‖ₑ + ‖⟪z, Ψ S x⟫_ℂ‖ₑ := enorm_sub_le
      _ ≤ ‖x‖ₑ * ‖z‖ₑ * traceNorm (Φ S) + ‖x‖ₑ * ‖z‖ₑ * traceNorm (Ψ S) :=
          add_le_add (enorm_inner_apply_le _ _ _) (enorm_inner_apply_le _ _ _)
      _ ≤ ‖x‖ₑ * ‖z‖ₑ * (c * traceNorm S) + ‖x‖ₑ * ‖z‖ₑ * (c' * traceNorm S) := by
          gcongr
          · exact hc S hS
          · exact hc' S hS
      _ = M * traceNorm S := by simp only [M]; ring
  -- `f` vanishes on all rank-one operators
  have hrk : ∀ u v : H, f (InnerProductSpace.rankOne ℂ u v) = 0 := by
    have bd : ∀ u v : H, ‖f (InnerProductSpace.rankOne ℂ u v)‖ ≤ M.toReal * ‖v‖ * ‖u‖ := by
      intro u v
      have h1 : ‖f (InnerProductSpace.rankOne ℂ u v)‖ₑ ≤ M * (‖u‖ₑ * ‖v‖ₑ) :=
        (fbd _ (rankOne_mem u v)).trans (mul_le_mul' le_rfl (traceNorm_rankOne_le u v))
      have h2 := ENNReal.toReal_mono
        (ENNReal.mul_ne_top hMtop (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)) h1
      simp only [ENNReal.toReal_mul, toReal_enorm] at h2
      linarith [h2]
    have step1 : ∀ j u, f (InnerProductSpace.rankOne ℂ u (b j)) = 0 := by
      intro j
      refine eq_zero_of_basis b (fun u => f (InnerProductSpace.rankOne ℂ u (b j))) ?_ ?_
        (M.toReal * ‖b j‖) (fun u => bd u (b j)) (fun i => by simp [hf, h i j])
      · intro u v; rw [map_add, add_apply]; exact fadd _ (rankOne_mem _ _) _ (rankOne_mem _ _)
      · intro a u; rw [map_smul, smul_apply]; exact fsmul a _ (rankOne_mem _ _)
    intro u
    have := eq_zero_of_basis b (fun v => star (f (InnerProductSpace.rankOne ℂ u v))) ?_ ?_
      (M.toReal * ‖u‖) ?_ (fun j => by simp [step1 j u])
    · intro v; simpa using this v
    · intro v w; rw [map_add, fadd _ (rankOne_mem _ _) _ (rankOne_mem _ _), star_add]
    · intro a v
      rw [map_smulₛₗ, fsmul _ _ (rankOne_mem _ _), star_mul, starRingEnd_apply, star_star,
        mul_comm]
    · intro v; rw [norm_star]
      have := bd u v; nlinarith [norm_nonneg u, norm_nonneg v, ENNReal.toReal_nonneg (a := M)]
  -- `f` vanishes on finite sums of rank-ones
  have hfin : ∀ {ι' : Type u} (F : Finset ι') (s : ι' → ℂ) (u v : ι' → H),
      f (∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n)) = 0 ∧
        ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n) ∈ traceClass H := by
    intro ι' F s u v
    classical
    induction F using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simp⟩
      simpa [Finset.sum_empty] using (fsmul 0 0 (zero_mem _)).trans (zero_mul _)
    | insert n F hn ih =>
      rw [Finset.sum_insert hn]
      have hm : s n • InnerProductSpace.rankOne ℂ (u n) (v n) ∈ traceClass H :=
        Submodule.smul_mem _ _ (rankOne_mem _ _)
      refine ⟨?_, add_mem hm ih.2⟩
      rw [fadd _ hm _ ih.2, fsmul _ _ (rankOne_mem _ _), hrk, ih.1]; simp
  -- trace-norm approximation
  obtain ⟨ι', v, u, s, -, -, -, -, ht⟩ := PFUL.Polar.schmidt_traceNorm hT
  have hbound : ∀ F : Finset ι', ‖f T‖ₑ ≤
      M * traceNorm (T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n)) := by
    intro F
    obtain ⟨h0, hmem⟩ := hfin F s u v
    have e : f T = f (T - ∑ n ∈ F, s n • InnerProductSpace.rankOne ℂ (u n) (v n)) := by
      have := fadd _ (sub_mem hT hmem) _ hmem
      rw [sub_add_cancel, h0, add_zero] at this; exact this
    rw [e]; exact fbd _ (sub_mem hT hmem)
  have hlim := ENNReal.Tendsto.const_mul ht (Or.inr hMtop)
  rw [mul_zero] at hlim
  have : ‖f T‖ₑ ≤ 0 := ge_of_tendsto' hlim hbound
  simpa using this

end PFUL.TraceClass
