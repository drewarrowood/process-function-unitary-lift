/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13, gap (a): the link product with ancillas of any cardinality

The link product `PFUL.PM.link W C` is a finite sum over the wires of `W`, so it is defined for
local Choi kernels `C_k` on ancilla types `X_k`, `Y_k` of any cardinality. Here:

* `IsCPTPKer J` : CPTP Choi kernel on arbitrary alphabets (PSD in Mathlib's `Finsupp` sense,
  i.e. all finite sections PSD; trace preservation as an unconditional sum).
* `IsValidPMInf W` : AFNB validity against CPTP kernels on arbitrary ancillas.
* `UnitaryLinkInf W` / `IsPurePMInf W` : AFNB purity against unitary kernels (orthonormal rows
  and columns, as unconditional sums) on arbitrary ancillas.
* `isValidPMInf_iff` : `IsValidPMInf W ↔ IsValidPM W` (every finite `W`).
* `isPurePMInf_iff σ` : `IsPurePMInf W ↔ IsPurePM W` (every finite `W`, with `σ k : I k ≃ O k`).

Proof ingredients: `posSemidef_of_sections` and `link_posSemidef_any` (positivity is a property
of finite sections), `psd_norm_le` (`|J p q| ≤ (J p p + J q q)/2`, giving absolute summability
of the partial traces), `reduceKer` (restrict the input ancilla to the two relevant values and
trace out the output ancilla: a finite CPTP Choi matrix with the same link entries),
`hasSum_pi_prod_any`, and the finite compression `exists_finite_compression` of Round 13 (b)
applied to the process-matrix loop `lmat U A`.
-/
import PFUL.AFNBPure
import PFUL.PureFiniteInf

open Matrix Finset
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PFUL.PM

theorem psd_norm_le {n : Type*} {J : Matrix n n ℂ} (hJ : J.PosSemidef) (p q : n) :
    ‖J p q‖ ≤ ((J p p).re + (J q q).re) / 2 := by
  classical
  have hpp := Complex.nonneg_iff.1 (hJ.diag_nonneg (i := p))
  have hqq := Complex.nonneg_iff.1 (hJ.diag_nonneg (i := q))
  by_cases h0 : J p q = 0
  · rw [h0, norm_zero]; linarith [hpp.1, hqq.1]
  have hn : (0:ℝ) < ‖J p q‖ := norm_pos_iff.2 h0
  have hzn : ((‖J p q‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set w : ℂ := star (J p q) / (‖J p q‖ : ℂ) with hw
  have hzz : J p q * star (J p q) = ((‖J p q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsr : star ((‖J p q‖ : ℝ) : ℂ) = (‖J p q‖ : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hzw : J p q * w = (‖J p q‖ : ℂ) := by
    rw [hw, mul_div_assoc', hzz]; field_simp; push_cast; ring
  have hww : star w * w = 1 := by
    rw [hw, star_div₀, star_star, hsr, div_mul_div_comm, hzz]; field_simp; push_cast; ring
  have hqp : J q p = star (J p q) := (hJ.1.apply q p).symm
  let f : Bool → n := fun b => if b then q else p
  have hK := (hJ.submatrix f).dotProduct_mulVec_nonneg (fun b => if b then -w else 1)
  simp only [dotProduct, mulVec, Fintype.sum_bool, f, submatrix_apply, ite_true, ite_false,
    Pi.star_apply, star_one, star_neg, Bool.false_eq_true] at hK
  have hsw : star w * star (J p q) = (‖J p q‖ : ℂ) := by
    rw [mul_comm, ← star_mul', hzw, hsr]
  have hE : -star w * (J q q * -w + J q p * 1) + 1 * (J p q * -w + J p p * 1) =
      J p p + J q q - 2 * (‖J p q‖ : ℂ) := by
    rw [hqp]; linear_combination (J q q) * hww - hsw - hzw
  rw [hE] at hK
  have := (Complex.nonneg_iff.1 hK).1
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at this
  norm_num at this
  linarith

/-- A matrix on an arbitrary index type is PSD (Mathlib's `Finsupp` definition) as soon as all
its finite principal sections are. -/
theorem posSemidef_of_sections {n : Type*} (M : Matrix n n ℂ)
    (h : ∀ S : Finset n, (M.submatrix ((↑) : S → n) ((↑) : S → n)).PosSemidef) :
    M.PosSemidef := by
  classical
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    have := (h {i, j}).1.apply ⟨i, by simp⟩ ⟨j, by simp⟩
    simpa [Matrix.conjTranspose_apply] using this
  · have hS := (h x.support).dotProduct_mulVec_nonneg (fun i => x i)
    simp only [dotProduct, mulVec, submatrix_apply, Pi.star_apply, Finset.mul_sum] at hS
    rw [Finset.sum_coe_sort x.support (fun i => ∑ j : x.support, star (x i) * (M i j * x j))] at hS
    convert hS using 1
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort x.support]
    exact Finset.sum_congr rfl fun j _ => by ring

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I O : ι → Type}
  [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
  {P F : Type} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]

/-- **Positivity of the link product, ancillas of any cardinality.** -/
theorem link_posSemidef_any {W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ} (hW : W.PosSemidef)
    {X Y : ι → Type} [∀ k, DecidableEq (X k)] [∀ k, DecidableEq (Y k)]
    {C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ}
    (hC : ∀ k, (C k).PosSemidef) : (link W C).PosSemidef := by
  classical
  refine posSemidef_of_sections _ fun S => ?_
  let X' : ι → Type := fun k => ↥(S.image fun z => z.1.2 k)
  let Y' : ι → Type := fun k => ↥(S.image fun z => z.2.2 k)
  let e : ∀ k, (I k × X' k) × (O k × Y' k) → (I k × X k) × (O k × Y k) :=
    fun k p => ((p.1.1, p.1.2.1), (p.2.1, p.2.2.1))
  have hL := link_posSemidef hW (X := X') (Y := Y') (C := fun k => (C k).submatrix (e k) (e k))
    fun k => (hC k).submatrix (e k)
  let j : S → (P × ∀ k, X' k) × (F × ∀ k, Y' k) := fun z =>
    ((z.1.1.1, fun k => ⟨z.1.1.2 k, Finset.mem_image_of_mem _ z.2⟩),
      (z.1.2.1, fun k => ⟨z.1.2.2 k, Finset.mem_image_of_mem _ z.2⟩))
  convert hL.submatrix j using 1
  ext z z'; rfl

/-! ## Sums over finite products of arbitrary index types -/

/-- Factorisation of absolutely summable families over `∀ k, κ k`, `ι` finite, the `κ k`
arbitrary (no countability). -/
theorem hasSum_pi_prod_any {ι : Type} [Fintype ι] {κ : ι → Type} (g : ∀ k, κ k → ℂ)
    (hg : ∀ k, Summable fun b => ‖g k b‖) :
    HasSum (fun β : (∀ k, κ k) => ∏ k, g k (β k)) (∏ k, ∑' b, g k b) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨-, h⟩ := PFUL.Counterexample.hasSum_pi_prod (Fintype.card ι) (κ := fun j => κ (e.symm j))
    (fun j => g (e.symm j)) (fun j => ∑' b, g (e.symm j) b) (fun j => hg _)
    (fun j => (hg _).of_norm.hasSum)
  have h1 : (fun β : (∀ k, κ k) => ∏ k, g k (β k)) =
      (fun β' : (∀ j, κ (e.symm j)) => ∏ j, g (e.symm j) (β' j)) ∘ (Equiv.piCongrLeft' κ e) := by
    funext β
    simp only [Function.comp_apply, Equiv.piCongrLeft'_apply]
    exact (Equiv.prod_comp e.symm (fun k => g k (β k))).symm
  rw [h1, (Equiv.piCongrLeft' κ e).hasSum_iff]
  convert h using 1
  exact (Equiv.prod_comp e.symm (fun k => ∑' b, g k b)).symm

/-! ## CPTP kernels on arbitrary alphabets -/

/-- Choi kernel (index `in × out`) of a CPTP map with alphabets of any cardinality: PSD in
Mathlib's sense (all finite sections) and `Σ_b J (a,b) (a',b) = δ_{aa'}` as an unconditional
sum. -/
def IsCPTPKer {A B : Type} [DecidableEq A] (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  J.PosSemidef ∧ ∀ a a', HasSum (fun b => J (a, b) (a', b)) (if a = a' then 1 else 0)

theorem IsCPTPChoi.isCPTPKer {A B : Type} [Fintype B] [DecidableEq A]
    {J : Matrix (A × B) (A × B) ℂ} (h : IsCPTPChoi J) : IsCPTPKer J :=
  ⟨h.1, fun a a' => by rw [← h.2 a a']; exact hasSum_fintype _⟩

theorem IsCPTPKer.isCPTPChoi {A B : Type} [Fintype B] [DecidableEq A]
    {J : Matrix (A × B) (A × B) ℂ} (h : IsCPTPKer J) : IsCPTPChoi J :=
  ⟨h.1, fun a a' => (hasSum_fintype _).unique (h.2 a a')⟩

theorem isCPTPKer_iff {A B : Type} [Fintype B] [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) : IsCPTPKer J ↔ IsCPTPChoi J :=
  ⟨IsCPTPKer.isCPTPChoi, IsCPTPChoi.isCPTPKer⟩

/-- The cross terms of the partial trace over an arbitrary output ancilla are absolutely
summable. -/
theorem IsCPTPKer.summable_norm {A B Y : Type} [DecidableEq A]
    {J : Matrix (A × (B × Y)) (A × (B × Y)) ℂ} (hJ : IsCPTPKer J) (a a' : A) (b b' : B) :
    Summable fun y => ‖J (a, (b, y)) (a', (b', y))‖ := by
  have hd : ∀ a b, Summable fun y => (J (a, (b, y)) (a, (b, y))).re := by
    intro a b
    have := ((hJ.2 a a).summable.comp_injective
      (Prod.mk_right_injective b : Function.Injective fun y : Y => (b, y)))
    exact Complex.reCLM.summable this
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun y => psd_norm_le hJ.1 (a, (b, y)) (a', (b', y))) ((((hd a b).add (hd a' b'))).div_const 2)
    |>.congr fun _ => rfl

/-- Restrict the input ancilla along `e` and trace out the output ancilla completely
(`Y ↦ Unit`): `J̃((a,x),(b,∗))((a',x'),(b',∗)) = Σ_y J((a,e x),(b,y))((a',e x'),(b',y))`. -/
noncomputable def reduceKer {A B X Y X' : Type} (J : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ)
    (e : X' → X) : Matrix ((A × X') × (B × Unit)) ((A × X') × (B × Unit)) ℂ :=
  fun r c => ∑' y, J ((r.1.1, e r.1.2), (r.2.1, y)) ((c.1.1, e c.1.2), (c.2.1, y))

theorem isCPTPChoi_reduceKer {A B X Y X' : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [Fintype X'] [DecidableEq X'] [DecidableEq X]
    {J : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ} (hJ : IsCPTPKer J) {e : X' → X}
    (he : Function.Injective e) : IsCPTPChoi (reduceKer J e) := by
  classical
  have hs : ∀ r c : (A × X') × (B × Unit), HasSum
      (fun y => J ((r.1.1, e r.1.2), (r.2.1, y)) ((c.1.1, e c.1.2), (c.2.1, y)))
      (reduceKer J e r c) := fun r c =>
    (hJ.summable_norm (r.1.1, e r.1.2) (c.1.1, e c.1.2) r.2.1 c.2.1).of_norm.hasSum
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩, fun a a' => ?_⟩
  · ext r c
    simp only [conjTranspose_apply, reduceKer, tsum_star]
    exact tsum_congr fun y => hJ.1.1.apply _ _
  · let q : Y → ((A × X') × (B × Unit)) → (A × X) × (B × Y) :=
      fun y r => ((r.1.1, e r.1.2), (r.2.1, y))
    have h1 : HasSum (fun y => ∑ r, ∑ c, star (v r) * (J (q y r) (q y c) * v c))
        (∑ r, ∑ c, star (v r) * (reduceKer J e r c * v c)) :=
      hasSum_sum fun r _ => hasSum_sum fun c _ => ((hs r c).mul_right (v c)).mul_left (star (v r))
    have h2 : star v ⬝ᵥ (reduceKer J e *ᵥ v) =
        ∑ r, ∑ c, star (v r) * (reduceKer J e r c * v c) := by
      simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    rw [h2]
    refine h1.nonneg fun y => ?_
    have := (hJ.1.submatrix (q y)).dotProduct_mulVec_nonneg v
    simpa only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, submatrix_apply] using this
  · have hfib : ∀ b, HasSum (fun y => J ((a.1, e a.2), (b, y)) ((a'.1, e a'.2), (b, y)))
        (reduceKer J e ((a.1, a.2), (b, ())) ((a'.1, a'.2), (b, ()))) := fun b => hs _ _
    have h := (hJ.2 (a.1, e a.2) (a'.1, e a'.2)).prod_fiberwise hfib
    rw [Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [(hasSum_fintype _).unique h]
    refine if_congr ?_ rfl rfl
    exact ⟨fun h' => by
        simp only [Prod.mk.injEq] at h'; exact Prod.ext h'.1 (he h'.2),
      fun h' => by rw [h']⟩

/-! ## Validity with ancillas of any cardinality -/

/-- **AFNB validity, ancillas of any cardinality**: `W ≥ 0`, and the link with CPTP kernels on
arbitrary (possibly uncountable) input and output ancillas `X_k`, `Y_k` is a CPTP kernel. The
link product `link` is a finite sum over the wires, so it needs no finiteness of `X_k`, `Y_k`. -/
def IsValidPMInf (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  W.PosSemidef ∧ ∀ (X Y : ι → Type) [∀ k, DecidableEq (X k)] [∀ k, DecidableEq (Y k)]
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ),
    (∀ k, IsCPTPKer (C k)) → IsCPTPKer (link W C)

theorem IsValidPMInf.isValidPM {W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ}
    (h : IsValidPMInf W) : IsValidPM W := by
  refine ⟨h.1, fun X Y _ _ _ _ C hC => ?_⟩
  exact (h.2 X Y C fun k => (hC k).isCPTPKer).isCPTPChoi

/-- **Finite ancillas suffice**: AFNB validity with finite ancillas implies validity with
ancillas of any cardinality. Positivity: every finite section of the infinite link is a
section of a finite link (`link_posSemidef_any`). Trace preservation: for given inputs
`ξ, ξ'`, restrict the input ancillas to `{ξ_k, ξ'_k}` and trace out the output ancillas
completely (`reduceKer`); the resulting finite CPTP Choi matrices have the same link entries,
by the factorisation of absolutely summable sums over `∀ k, Y_k` (`hasSum_pi_prod_any`). -/
theorem IsValidPM.isValidPMInf {W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ}
    (h : IsValidPM W) : IsValidPMInf W := by
  refine ⟨h.1, fun X Y _ _ C hC => ⟨link_posSemidef_any h.1 fun k => (hC k).1, ?_⟩⟩
  rintro ⟨π, ξ⟩ ⟨π', ξ'⟩
  classical
  let X' : ι → Type := fun k => ↥({ξ k, ξ' k} : Finset (X k))
  let C' := fun k => reduceKer (C k) (Subtype.val : X' k → X k)
  have hC' : ∀ k, IsCPTPChoi (C' k) := fun k => isCPTPChoi_reduceKer (hC k) Subtype.val_injective
  let ξt : ∀ k, X' k := fun k => ⟨ξ k, by simp⟩
  let ξt' : ∀ k, X' k := fun k => ⟨ξ' k, by simp⟩
  have hV := (h.2 X' (fun _ => Unit) C' hC').2 (π, ξt) (π', ξt')
  have hfib : ∀ φ, HasSum (fun η : ∀ k, Y k => link W C ((π, ξ), (φ, η)) ((π', ξ'), (φ, η)))
      (∑ u : (∀ k, Unit), link W C' ((π, ξt), (φ, u)) ((π', ξt'), (φ, u))) := by
    intro φ
    simp only [Finset.univ_unique, Finset.sum_singleton]
    refine hasSum_sum fun a _ => hasSum_sum fun a' _ => HasSum.mul_left _ ?_
    exact hasSum_pi_prod_any
      (fun k y => C k (((a k).1, ξ k), ((a k).2, y)) (((a' k).1, ξ' k), ((a' k).2, y)))
      (fun k => (hC k).summable_norm _ _ _ _)
  have := PFUL.Counterexample.hasSum_prod_fintype
    (fun b : F × (∀ k, Y k) => link W C ((π, ξ), b) ((π', ξ'), b)) _ hfib
  rw [← Fintype.sum_prod_type' (f := fun φ u => link W C' ((π, ξt), (φ, u)) ((π', ξt'), (φ, u)))]
    at this
  convert this using 1
  rw [hV]
  refine if_congr ?_ rfl rfl
  constructor
  · intro h'
    simp only [Prod.mk.injEq] at h' ⊢
    exact ⟨h'.1, funext fun k => Subtype.ext (congrFun h'.2 k)⟩
  · intro h'
    simp only [Prod.mk.injEq] at h' ⊢
    exact ⟨h'.1, funext fun k => congrArg Subtype.val (congrFun h'.2 k)⟩

/-- **(a) Validity: finite and infinite ancillas agree.** -/
theorem isValidPMInf_iff (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) :
    IsValidPMInf W ↔ IsValidPM W :=
  ⟨IsValidPMInf.isValidPM, IsValidPM.isValidPMInf⟩

/-! ## Purity with ancillas of any cardinality -/

open PFUL.Counterexample (IsIsoKernel IsCoIsoKernel summable_star_mul summable_sq_of_isIsoKernel
  exists_finite_compression isCoIsoKernel_iff_isIsoKernel_conjTranspose)

theorem isIsoKernel_of_mul {R C : Type} [Fintype R] [DecidableEq C] {A : Matrix R C ℂ}
    (h : Aᴴ * A = 1) : IsIsoKernel A := by
  intro c c'
  have := congrFun (congrFun h c) c'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Matrix.conjTranspose_apply] at this
  rw [← this]; exact hasSum_fintype _

theorem mul_of_isIsoKernel {R C : Type} [Fintype R] [DecidableEq C] {A : Matrix R C ℂ}
    (h : IsIsoKernel A) : Aᴴ * A = 1 := by
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  exact (hasSum_fintype _).unique (h c c')

theorem isUnitaryM_iff_kernel {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℂ) : IsUnitaryM A ↔ IsIsoKernel A ∧ IsCoIsoKernel A := by
  rw [isCoIsoKernel_iff_isIsoKernel_conjTranspose]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨isIsoKernel_of_mul h1, isIsoKernel_of_mul (by rw [conjTranspose_conjTranspose]; exact h2)⟩
  · rintro ⟨h1, h2⟩
    have := mul_of_isIsoKernel h2
    rw [conjTranspose_conjTranspose] at this
    exact ⟨mul_of_isIsoKernel h1, this⟩

/-- The matrix `M = U ∗ A` of the map `P ⊗ X → F ⊗ X` obtained by inserting the local maps
`A_k : I_k ⊗ X_k → O_k ⊗ X_k` into `U : P ⊗ O → F ⊗ I` (ancillas of any cardinality). -/
def lmat (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) {X : ι → Type}
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ) : Matrix (F × ∀ k, X k) (P × ∀ k, X k) ℂ :=
  fun r c => ∑ a : (∀ k, I k × O k), U (r.1, fun k => (a k).1) (c.1, fun k => (a k).2) *
    ∏ k, A k ((a k).2, r.2 k) ((a k).1, c.2 k)

theorem link_choiPM_vecOp (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) {X : ι → Type}
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ) :
    link (choiPM U) (fun k => vecOp (A k)) = vecOp (lmat U A) :=
  link_rankOne (pvec U) (fun k => vecOf (A k))

/-- Local Gram numbers. -/
noncomputable def gramA {Ik Ok Xk : Type} (A : Matrix (Ok × Xk) (Ik × Xk) ℂ) (ξ ξ' : Xk)
    (a a' : Ik × Ok) : ℂ :=
  ∑' y, star (A (a.2, y) (a.1, ξ)) * A (a'.2, y) (a'.1, ξ')

/-- The Gram entries of `lmat U A` as a polynomial in the local Gram numbers. -/
noncomputable def gramU (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) (π π' : P)
    (G : ∀ k, I k × O k → I k × O k → ℂ) : ℂ :=
  ∑ φ : F, ∑ a : (∀ k, I k × O k), ∑ a' : (∀ k, I k × O k),
    star (U (φ, fun k => (a k).1) (π, fun k => (a k).2)) *
      U (φ, fun k => (a' k).1) (π', fun k => (a' k).2) * ∏ k, G k (a k) (a' k)

theorem hasSum_gramU (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) {X : ι → Type}
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ)
    (hsq : ∀ k (c : I k × X k) (o : O k), Summable fun y => ‖A k (o, y) c‖ ^ 2)
    (π π' : P) (ξ ξ' : ∀ k, X k) :
    HasSum (fun r : F × (∀ k, X k) => star (lmat U A r (π, ξ)) * lmat U A r (π', ξ'))
      (gramU U π π' fun k => gramA (A k) (ξ k) (ξ' k)) := by
  apply PFUL.Counterexample.hasSum_prod_fintype
  intro φ
  have expand : ∀ η : ∀ k, X k,
      star (lmat U A (φ, η) (π, ξ)) * lmat U A (φ, η) (π', ξ') =
        ∑ a : (∀ k, I k × O k), ∑ a' : (∀ k, I k × O k),
          star (U (φ, fun k => (a k).1) (π, fun k => (a k).2)) *
            U (φ, fun k => (a' k).1) (π', fun k => (a' k).2) *
            ∏ k, (star (A k ((a k).2, η k) ((a k).1, ξ k)) *
              A k ((a' k).2, η k) ((a' k).1, ξ' k)) := by
    intro η
    simp only [lmat, star_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.prod_mul_distrib, star_mul', star_prod]
    ring
  rw [show (fun η : ∀ k, X k => star (lmat U A (φ, η) (π, ξ)) * lmat U A (φ, η) (π', ξ'))
      = _ from funext expand]
  refine hasSum_sum fun a _ => hasSum_sum fun a' _ => HasSum.mul_left _ ?_
  exact hasSum_pi_prod_any (fun k y => star (A k ((a k).2, y) ((a k).1, ξ k)) *
      A k ((a' k).2, y) ((a' k).1, ξ' k)) fun k => summable_star_mul (hsq k _ _) (hsq k _ _)

/-- Purity of `U` against finite local unitaries. -/
def FinPureU (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) : Prop :=
  ∀ (X : ι → Type) [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ), (∀ k, IsUnitaryM (A k)) → IsUnitaryM (lmat U A)

theorem finPureU_of_unitaryLink {U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ}
    (h : UnitaryLink (choiPM U)) : FinPureU U := by
  intro X _ _ A hA
  obtain ⟨M, hM, hl⟩ := h X A hA
  exact isUnitaryM_of_vecOp_eq hM ((link_choiPM_vecOp U A).symm.trans hl)

/-- **Compression step**: finite purity of `U` makes `U ∗ A` isometric for isometric kernels
`A_k` on ancillas of any cardinality. -/
theorem isIsoKernel_lmat (σ : ∀ k, I k ≃ O k) {U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ}
    (hU : FinPureU U) {X : ι → Type} [∀ k, DecidableEq (X k)]
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ) (hA : ∀ k, IsIsoKernel (A k)) :
    IsIsoKernel (lmat U A) := by
  classical
  have hsq : ∀ k (c : I k × X k) (o : O k), Summable fun y => ‖A k (o, y) c‖ ^ 2 :=
    fun k c o => (summable_sq_of_isIsoKernel (hA k) c).comp_injective (Prod.mk_right_injective o)
  rintro ⟨π, ξ⟩ ⟨π', ξ'⟩
  choose n hn hd B i j hBB hBB' hij hg using fun k =>
    exists_finite_compression (σ k) (A k) (hA k) (ξ k) (ξ' k)
  let _ : ∀ k, Fintype (n k) := hn
  let _ : ∀ k, DecidableEq (n k) := hd
  have hG : (fun k => gramA (B k) (i k) (j k)) = fun k => gramA (A k) (ξ k) (ξ' k) := by
    funext k a a'
    simp only [gramA]
    rw [tsum_fintype, (hg k _ _ _ _).tsum_eq]
  have hBsq : ∀ k (c : I k × n k) (o : O k), Summable fun y => ‖B k (o, y) c‖ ^ 2 :=
    fun k c o => (summable_sq_of_isIsoKernel (isIsoKernel_of_mul (hBB k)) c).comp_injective
      (Prod.mk_right_injective o)
  have h1 := hasSum_gramU U B hBsq π π' i j
  rw [hG] at h1
  have hM := hU n B fun k => ⟨hBB k, hBB' k⟩
  have h2 := isIsoKernel_of_mul hM.1 (π, i) (π', j)
  have hval := h1.unique h2
  have hidx : ((π, i) = (π', j)) ↔ ((π, ξ) = (π', ξ')) := by
    simp only [Prod.mk.injEq, funext_iff]
    exact and_congr Iff.rfl (forall_congr' fun k => hij k)
  have := hasSum_gramU U A hsq π π' ξ ξ'
  rwa [hval, if_congr hidx rfl rfl] at this

/-- `(U ∗ A)† = U† ∗ A†`, with the roles of inputs and outputs exchanged. -/
theorem lmat_conjTranspose (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) {X : ι → Type}
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ) :
    (lmat U A)ᴴ = lmat (I := O) (O := I) (P := F) (F := P) Uᴴ (fun k => (A k)ᴴ) := by
  ext r c
  simp only [conjTranspose_apply, lmat, star_sum, star_mul', star_prod]
  exact Fintype.sum_equiv (Equiv.piCongrRight fun k => Equiv.prodComm (I k) (O k)) _ _
    fun a => rfl

theorem FinPureU.conjTranspose {U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ} (hU : FinPureU U) :
    FinPureU (I := O) (O := I) (P := F) (F := P) Uᴴ := by
  intro X _ _ B hB
  have hB' : ∀ k, IsUnitaryM (B k)ᴴ := fun k =>
    ⟨by rw [conjTranspose_conjTranspose]; exact (hB k).2, by
      rw [conjTranspose_conjTranspose]; exact (hB k).1⟩
  have h := hU X (fun k => (B k)ᴴ) hB'
  have he := lmat_conjTranspose U (fun k => (B k)ᴴ)
  simp only [conjTranspose_conjTranspose] at he
  rw [← he]
  exact ⟨by rw [conjTranspose_conjTranspose]; exact h.2, by rw [conjTranspose_conjTranspose]; exact h.1⟩

/-- **Finite purity of `U` gives unitary kernels `U ∗ A` for unitary kernels `A_k` on ancillas
of any cardinality** (isometry by compression; co-isometry by the same argument for `U†`). -/
theorem isUnitaryKer_lmat (σ : ∀ k, I k ≃ O k) {U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ}
    (hU : FinPureU U) {X : ι → Type} [∀ k, DecidableEq (X k)]
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ) (hc : ∀ k, IsIsoKernel (A k))
    (hr : ∀ k, IsCoIsoKernel (A k)) :
    IsIsoKernel (lmat U A) ∧ IsCoIsoKernel (lmat U A) := by
  refine ⟨isIsoKernel_lmat σ hU A hc, ?_⟩
  rw [isCoIsoKernel_iff_isIsoKernel_conjTranspose, lmat_conjTranspose]
  exact isIsoKernel_lmat (fun k => (σ k).symm) hU.conjTranspose _ fun k =>
    (isCoIsoKernel_iff_isIsoKernel_conjTranspose _).1 (hr k)

/-- **AFNB purity, ancillas of any cardinality**: the link with local unitary kernels (columns
and rows orthonormal, as unconditional sums) on arbitrary ancillas `X_k` is the Choi
projector `|M⟩⟩⟨⟨M|` of a unitary kernel `M`. -/
def UnitaryLinkInf (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  ∀ (X : ι → Type) [∀ k, DecidableEq (X k)] (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ),
    (∀ k, IsIsoKernel (A k)) → (∀ k, IsCoIsoKernel (A k)) →
    ∃ M : Matrix (F × ∀ k, X k) (P × ∀ k, X k) ℂ, IsIsoKernel M ∧ IsCoIsoKernel M ∧
      link W (fun k => vecOp (A k)) = vecOp M

def IsPurePMInf (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  IsValidPMInf W ∧ UnitaryLinkInf W

/-- **(a) Purity: finite and infinite ancillas agree** (`σ k : I k ≃ O k` as in AFNBPure). -/
theorem isPurePMInf_iff (σ : ∀ k, I k ≃ O k) (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) :
    IsPurePMInf W ↔ IsPurePM W := by
  constructor
  · rintro ⟨hv, hu⟩
    refine ⟨hv.isValidPM, fun X _ _ A hA => ?_⟩
    have hk := fun k => (isUnitaryM_iff_kernel (A k)).1 (hA k)
    obtain ⟨M, hMi, hMc, hM⟩ := hu X A (fun k => (hk k).1) (fun k => (hk k).2)
    exact ⟨M, (isUnitaryM_iff_kernel M).2 ⟨hMi, hMc⟩, hM⟩
  · rintro ⟨hv, hu⟩
    refine ⟨hv.isValidPMInf, ?_⟩
    obtain ⟨U, -, rfl⟩ := exists_unitary_of_unitaryLink σ hu
    have hU := finPureU_of_unitaryLink hu
    intro X _ A hc hr
    obtain ⟨h1, h2⟩ := isUnitaryKer_lmat σ hU A hc hr
    exact ⟨lmat U A, h1, h2, link_choiPM_vecOp U A⟩

end PFUL.PM
