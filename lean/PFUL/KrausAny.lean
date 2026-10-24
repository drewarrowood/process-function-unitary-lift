/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13, gap (d): Kraus theorem and normal-CPTP validity for ancillas of any cardinality

The countability hypotheses of `KernelPSD.exists_factor`, `exists_kraus_of_choi`,
`exists_kraus_of_normalCPTP`, `isNormalCPTP_iff_kraus` and `valid_normalCPTP_Vsb` entered only
through the Gram–Schmidt construction of a Hilbert basis of the RKHS of the kernel along an
enumeration. Here that step is replaced by Mathlib's `exists_hilbertBasis` (Zorn), which gives
a Hilbert basis of any Hilbert space; everything else goes through unchanged.
-/
import PFUL.CounterexampleHilbert

open scoped InnerProductSpace ComplexOrder ComplexConjugate
open ContinuousLinearMap PFUL.TraceClass

set_option linter.unusedSectionVars false

universe u

namespace PFUL.Countable

/-- **Kolmogorov factorisation, any index set.** -/
theorem KernelPSD.exists_factor_any {P : Type u} [DecidableEq P] {J : P → P → ℂ}
    (hJ : KernelPSD J) :
    ∃ (Y : Type u) (W : P → Y → ℂ), ∀ p q, HasSum (fun y => W p y * star (W q y)) (J p q) := by
  classical
  let K : Matrix P P (ℂ →L[ℂ] ℂ) := Matrix.of fun x y => J y x • ContinuousLinearMap.id ℂ ℂ
  have hK : K.PosSemidef := by
    refine RKHS.posSemidef_iff_re_sum_kernel'.2 ⟨?_, fun vv => ?_⟩
    · ext i j : 1
      simp only [Matrix.conjTranspose_apply, K, Matrix.of_apply, star_smul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
      rw [hJ.herm i j]
    · have h0 := (Complex.nonneg_iff.1 (hJ vv.support fun p => star (vv p))).1
      convert h0 using 1
      simp only [Finsupp.sum, K, Matrix.of_apply, smul_apply,
        ContinuousLinearMap.id_apply, inner_smul_left, star_star]
      refine (congrArg Complex.re ?_).trans (Complex.conj_re _)
      simp only [map_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
      simp [RCLike.inner_apply]; ring
  haveI : Fact K.PosSemidef := ⟨hK⟩
  let H := RKHS.OfKernel K
  let φ : P → H := fun p => RKHS.kerFun H p 1
  have hφ : ∀ p q, J p q = ⟪φ q, φ p⟫_ℂ := by
    intro p q
    simp only [φ]
    rw [← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
    simp [K, RCLike.inner_apply]
    exact hJ.herm q p
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, fun p y => ⟪b y, φ p⟫_ℂ, fun p q => ?_⟩
  have := b.hasSum_inner_mul_inner (φ q) (φ p)
  rw [hφ]
  convert this using 1
  funext y
  simp only [Complex.star_def]
  rw [inner_conj_symm]
  ring

/-- **Converse Choi theorem, any alphabets.** -/
theorem exists_kraus_of_choi_any {O A : Type u} [DecidableEq O]
    [DecidableEq A] {J : O × A → O × A → ℂ} (hJ : KernelPSD J)
    (hTP : ∀ a a', HasSum (fun o => J (o, a) (o, a')) (if a' = a then 1 else 0)) :
    ∃ (Y : Type u) (V : O × Y → A → ℂ),
      (∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) ∧
      choiKernel V = J := by
  obtain ⟨Y, W, hW⟩ := hJ.exists_factor_any
  refine ⟨Y, fun r a => W (r.1, a) r.2, ?_, ?_⟩
  · have hsq : ∀ a, Summable fun r : O × Y => ‖W (r.1, a) r.2‖ ^ 2 := by
      intro a
      have hre : ∀ o, HasSum (fun y => ‖W (o, a) y‖ ^ 2) (J (o, a) (o, a)).re := by
        intro o
        have := Complex.reCLM.hasSum (hW (o, a) (o, a))
        convert this using 1
        · funext y
          simp [Complex.reCLM_apply, Complex.mul_conj, Complex.sq_norm]
        · rfl
      refine (summable_prod_of_nonneg fun r => by positivity).2 ⟨fun o => (hre o).summable, ?_⟩
      have := Complex.reCLM.hasSum (hTP a a)
      refine (this.congr_fun fun o => ?_).summable
      simp [(hre o).tsum_eq]
    intro a a'
    have hs : Summable fun r : O × Y => W (r.1, a') r.2 * star (W (r.1, a) r.2) :=
      summable_mul_star_of_sq (hsq a') (hsq a)
    have hfib : ∀ o, HasSum (fun y => W (o, a') y * star (W (o, a) y)) (J (o, a') (o, a)) :=
      fun o => hW _ _
    have h1 := hs.hasSum.prod_fiberwise hfib
    have h2 := (hTP a' a).unique h1
    convert hs.hasSum using 1
    · funext r; simp [mul_comm]
  · funext p q
    exact (hW p q).tsum_eq

end PFUL.Countable

open PFUL.Countable

/-- **Kraus representation of normal CPTP maps on `ℓ²` of any cardinality.** -/
theorem exists_kraus_of_normalCPTP_any {O A : Type u} [DecidableEq O]
    [DecidableEq A] {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
      (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} (hΦ : IsNormalCPTP Φ) :
    ∃ (Y : Type u) (_ : DecidableEq Y) (V : O × Y → A → ℂ)
      (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)),
      ∀ ρ ∈ traceClass (lp (fun _ : A => ℂ) 2), Φ ρ = krausChannel V hiso ρ := by
  classical
  obtain ⟨Y, V, hiso, hJ⟩ :=
    exists_kraus_of_choi_any (choiOf_psd hΦ.toIsCPTP) (choiOf_tp hΦ.toIsCPTP)
  refine ⟨Y, inferInstance, V, hiso, ?_⟩
  set bA := (default : HilbertBasis A ℂ (lp (fun _ : A => ℂ) 2))
  set bO := (default : HilbertBasis O ℂ (lp (fun _ : O => ℂ) 2))
  refine eq_of_rankOne_basis hΦ (isNormalCPTP_krausChannel V hiso) bA fun a a' => ?_
  refine clm_ext_entries bO bO fun o' o => ?_
  simp only [bA, bO, stdBasis_lp_apply]
  rw [inner_krausChannel, hJ]
  rfl

/-- **Kraus ⟺ normal CPTP on `ℓ²` of any cardinality.** -/
theorem isNormalCPTP_iff_kraus_any {O A : Type u} [DecidableEq O]
    [DecidableEq A] {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
      (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} :
    IsNormalCPTP Φ ↔ ∃ (Y : Type u) (_ : DecidableEq Y) (V : O × Y → A → ℂ)
      (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)),
      ∀ ρ ∈ traceClass (lp (fun _ : A => ℂ) 2), Φ ρ = krausChannel V hiso ρ := by
  refine ⟨exists_kraus_of_normalCPTP_any, ?_⟩
  rintro ⟨Y, _, V, hiso, h⟩
  exact (isNormalCPTP_krausChannel V hiso).congr h

namespace PFUL.Counterexample

/-- **Gap (d) closed: validity of the Switchboard against normal CPTP local channels on ancillas
of any cardinality** (no countability hypothesis). -/
theorem valid_normalCPTP_Vsb_any {X X' : Fin 3 → Type} [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (X' k)]
    (Φ : ∀ k, (lp (fun _ : Bool × X k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X k => ℂ) 2) →
      (lp (fun _ : Bool × X' k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X' k => ℂ) 2))
    (hΦ : ∀ k, IsNormalCPTP (Φ k)) :
    ∃ (Y : Fin 3 → Type) (_ : ∀ k, DecidableEq (Y k))
      (V : ∀ k, (Bool × X' k) × Y k → Bool × X k → ℂ)
      (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)),
      (∀ k, ∀ ρ ∈ traceClass (lp (fun _ : Bool × X k => ℂ) 2),
        Φ k ρ = krausChannel (V k) (hiso k) ρ) ∧
      IsNormalCPTP (krausChannel (krausLoop V) (isIsoKernel_krausLoop V hiso)) := by
  have hk := fun k => exists_kraus_of_normalCPTP_any (hΦ k)
  choose Y hYd V hiso hV using hk
  exact ⟨Y, hYd, V, hiso, hV, isNormalCPTP_krausChannel _ _⟩

end PFUL.Counterexample
