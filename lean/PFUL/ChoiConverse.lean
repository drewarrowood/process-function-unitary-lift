import PFUL.ChoiL2
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open scoped InnerProductSpace ComplexOrder ComplexConjugate
open InnerProductSpace (gramSchmidt gramSchmidtNormed gramSchmidtNormed_orthonormal' span_gramSchmidtNormed_range span_gramSchmidt)

set_option linter.unusedSectionVars false

namespace PFUL.Countable

/-- A kernel all of whose finite sections are positive semidefinite (in the complex order). -/
def KernelPSD {P : Type*} (J : P → P → ℂ) : Prop :=
  ∀ (s : Finset P) (c : P → ℂ), 0 ≤ ∑ p ∈ s, ∑ q ∈ s, star (c p) * J p q * c q

theorem KernelPSD.diag_im {P : Type*} {J : P → P → ℂ} (h : KernelPSD J) (p : P) :
    (J p p).im = 0 := by
  have := (Complex.nonneg_iff.1 (h {p} fun _ => 1)).2
  simpa using this.symm

theorem KernelPSD.herm {P : Type*} [DecidableEq P] {J : P → P → ℂ} (h : KernelPSD J) (p q : P) :
    J q p = star (J p q) := by
  by_cases hpq : p = q
  · subst hpq; apply Complex.ext <;> simp [h.diag_im p]
  have key : ∀ z : ℂ, (J p p + J p q * z + star z * J q p + star z * J q q * z).im = 0 := by
    intro z
    have := (Complex.nonneg_iff.1 (h {p, q} fun r => if r = p then 1 else z)).2
    rw [Finset.sum_pair hpq, Finset.sum_pair hpq, Finset.sum_pair hpq] at this
    simp only [if_neg (Ne.symm hpq), ite_true, star_one, one_mul, mul_one] at this
    rw [this]; congr 1; ring
  have h1 := key 1
  have h2 := key Complex.I
  have dp := h.diag_im p
  have dq := h.diag_im q
  simp [Complex.mul_im, Complex.add_im] at h1 h2
  apply Complex.ext <;> simp <;> linarith


universe u

/-- **Kolmogorov factorisation over a countable index.** A positive semidefinite kernel on a
countable set factors as `J p q = ∑_y W p y · conj (W q y)` over a countable index `Y`
(via Mathlib's Moore–Aronszajn RKHS and Gram–Schmidt over an enumeration). -/
theorem KernelPSD.exists_factor {P : Type u} [Countable P] [DecidableEq P] {J : P → P → ℂ}
    (hJ : KernelPSD J) :
    ∃ (Y : Type u) (_ : Countable Y) (W : P → Y → ℂ),
      ∀ p q, HasSum (fun y => W p y * star (W q y)) (J p q) := by
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
      simp only [Finsupp.sum, K, Matrix.of_apply, ContinuousLinearMap.smul_apply,
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
  haveI := Encodable.ofCountable P
  let f : ℕ → H := fun n => (Encodable.decode (α := P) n).elim 0 φ
  let e := gramSchmidtNormed ℂ f
  let Y := ULift.{u} {n : ℕ | e n ≠ 0}
  let v : Y → H := fun y => e y.down.1
  have hon : Orthonormal ℂ v :=
    (gramSchmidtNormed_orthonormal' f).comp _ ULift.down_injective
  have hspan : Submodule.span ℂ (Set.range e) ≤ Submodule.span ℂ (Set.range v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    by_cases hn : e n = 0
    · rw [hn]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨⟨n, hn⟩⟩, rfl⟩
  have hker : Submodule.span ℂ {x | ∃ p, ∃ c : ℂ, RKHS.kerFun H p c = x} ≤
      Submodule.span ℂ (Set.range e) := by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, c, rfl⟩
    have : RKHS.kerFun H p c = c • f (Encodable.encode p) := by
      simp only [f, Encodable.encodek, Option.elim_some, φ, ← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have htop : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [← RKHS.kerFun_dense (𝕜 := ℂ) H]
    exact Submodule.topologicalClosure_mono (hker.trans hspan)
  let b := HilbertBasis.mk hon htop
  refine ⟨Y, inferInstance, fun p y => ⟪b y, φ p⟫_ℂ, fun p q => ?_⟩
  have := b.hasSum_inner_mul_inner (φ q) (φ p)
  rw [hφ]
  convert this using 1
  funext y
  simp only [Complex.star_def]
  rw [inner_conj_symm]
  ring

/-- **Converse Choi theorem on countable alphabets.** Every kernel `J` on `O × A` all of whose
finite sections are positive semidefinite and which satisfies the trace-preservation condition
`∑_o J (o, a) (o, a') = δ_{a a'}` is the Choi kernel of a Kraus kernel `V` over a countable Kraus
index `Y`, with `∑_y K_y† K_y = 1` (`hiso`); so `valid_kraus_l2` applies to it. -/
theorem exists_kraus_of_choi {O A : Type u} [Countable O] [Countable A] [DecidableEq O]
    [DecidableEq A] {J : O × A → O × A → ℂ} (hJ : KernelPSD J)
    (hTP : ∀ a a', HasSum (fun o => J (o, a) (o, a')) (if a' = a then 1 else 0)) :
    ∃ (Y : Type u) (_ : Countable Y) (V : O × Y → A → ℂ),
      (∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) ∧
      choiKernel V = J := by
  obtain ⟨Y, hY, W, hW⟩ := hJ.exists_factor
  refine ⟨Y, hY, fun r a => W (r.1, a) r.2, ?_, ?_⟩
  · -- squared norms are summable on `O × Y`
    have hsq : ∀ a, Summable fun r : O × Y => ‖W (r.1, a) r.2‖ ^ 2 := by
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
