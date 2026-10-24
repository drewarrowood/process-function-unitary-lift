/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13, gap (b): finite purity implies purity with ancillas of any dimension

For **every** process `V : Proc P P` (binary parties, finite `P`):

* `isPureKer_of_isPure : IsPure V → IsPureKer V`
* `isUnitaryKer_of_isPure : IsPure V → IsUnitaryKer V`
* `isPureHilbert_of_isPure : IsPure V → IsPureHilbert V`
* `isPure_iff_isUnitaryKer`, `isPure_iff_isPureHilbert`.

Proof (H.19.4 of the paper): the Gram entry `⟪M e_c, M e_c'⟫` of the composed kernel
`M = compose V a` depends on the local kernels only through the finitely many cross Gram numbers
`Σ_b conj a_k (x,b)(y,α_k) · a_k (x',b)(y',α'_k)` (`hasSum_gram`). By
`exists_finite_compression` these are realised by a finite unitary `B_k` at two ancilla
levels `i_k, j_k` with `i_k = j_k ↔ α_k = α'_k`; finite purity of `V` then forces the Gram entry
to be `δ_{cc'}`. Rows follow by applying the same argument to `Vᴴ` and `aᴴ`
(`compose_conjTranspose`).
-/
import PFUL.Compression

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false

namespace PFUL.Counterexample

/-- Cross Gram number of a local kernel between the columns `(y, α)` and `(y', α')`, restricted
to the output wire values `x, x'`. -/
noncomputable def gramK {κ : Type} (a : Matrix (Bool × κ) (Bool × κ) ℂ) (α α' : κ)
    (x y x' y' : Bool) : ℂ :=
  ∑' b, star (a (x, b) (y, α)) * a (x', b) (y', α')

/-- The Gram entry of the composed kernel as a polynomial in the local Gram numbers. -/
noncomputable def gramV {P : Type} [Fintype P] (V : Proc P P) (π π' : P)
    (G : Fin 3 → Bool → Bool → Bool → Bool → ℂ) : ℂ :=
  ∑ φ : P, ∑ o : Fin 8, ∑ o' : Fin 8, ∑ e : Fin 8, ∑ e' : Fin 8,
    star (V (e, φ) (o, π)) * V (e', φ) (o', π') *
      ∏ k, G k (bit k o) (bit k e) (bit k o') (bit k e')

theorem hasSum_gram {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) {κ : Fin 3 → Type}
    (a : ∀ k, Matrix (Bool × κ k) (Bool × κ k) ℂ)
    (hsq : ∀ k (c : Bool × κ k) (x : Bool), Summable fun b => ‖a k (x, b) c‖ ^ 2)
    (π π' : P) (α α' : ∀ k, κ k) :
    HasSum (fun r : P × (∀ k, κ k) => star (compose V a r (π, α)) * compose V a r (π', α'))
      (gramV V π π' fun k => gramK (a k) (α k) (α' k)) := by
  apply hasSum_prod_fintype
  intro φ
  have expand : ∀ β : ∀ k, κ k,
      star (compose V a (φ, β) (π, α)) * compose V a (φ, β) (π', α') =
        ∑ o : Fin 8, ∑ o' : Fin 8, ∑ e : Fin 8, ∑ e' : Fin 8,
          star (V (e, φ) (o, π)) * V (e', φ) (o', π') *
            ∏ k, (star (a k (bit k o, β k) (bit k e, α k)) *
              a k (bit k o', β k) (bit k e', α' k)) := by
    intro β
    simp only [compose, star_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
    rw [Finset.prod_mul_distrib, star_mul', star_prod]
    ring
  rw [show (fun β : ∀ k, κ k => star (compose V a (φ, β) (π, α)) * compose V a (φ, β) (π', α'))
      = _ from funext expand]
  refine hasSum_sum fun o _ => hasSum_sum fun o' _ => hasSum_sum fun e _ =>
    hasSum_sum fun e' _ => ?_
  refine (hasSum_pi_prod 3 (fun k b => star (a k (bit k o, b) (bit k e, α k)) *
      a k (bit k o', b) (bit k e', α' k)) _ (fun k => ?_) (fun k => ?_)).2.mul_left _
  · exact summable_star_mul (hsq k _ _) (hsq k _ _)
  · exact (summable_star_mul (hsq k _ _) (hsq k _ _)).of_norm.hasSum

theorem isIsoKernel_of_conjTranspose_mul {X : Type} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} (h : A.conjTranspose * A = 1) : IsIsoKernel A := by
  intro c c'
  have := congrFun (congrFun h c) c'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Matrix.conjTranspose_apply] at this
  rw [← this]; exact hasSum_fintype _

theorem conjTranspose_mul_of_isIsoKernel {X : Type} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} (h : IsIsoKernel A) : A.conjTranspose * A = 1 := by
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  exact (hasSum_fintype _).unique (h c c')

/-- **Finite purity gives isometric composition with isometric kernels on ancillas of any
cardinality.** -/
theorem isPureKer_of_isPure {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (hV : IsPure V) : IsPureKer V := by
  classical
  intro κ _ a ha
  have hsq : ∀ k (c : Bool × κ k) (x : Bool), Summable fun b => ‖a k (x, b) c‖ ^ 2 :=
    fun k c x => (summable_sq_of_isIsoKernel (ha k) c).comp_injective (Prod.mk_right_injective x)
  rintro ⟨π, α⟩ ⟨π', α'⟩
  choose n hn hd B i j hBB hBB' hij hg using fun k =>
    exists_finite_compression (Equiv.refl Bool) (a k) (ha k) (α k) (α' k)
  let _ : ∀ k, Fintype (n k) := hn
  let _ : ∀ k, DecidableEq (n k) := hd
  have hG : (fun k => gramK (B k) (i k) (j k)) = fun k => gramK (a k) (α k) (α' k) := by
    funext k x y x' y'
    simp only [gramK]
    rw [tsum_fintype, (hg k x y x' y').tsum_eq]
  have hBsq : ∀ k (c : Bool × n k) (x : Bool), Summable fun b => ‖B k (x, b) c‖ ^ 2 :=
    fun k c x => (summable_sq_of_isIsoKernel (isIsoKernel_of_conjTranspose_mul (hBB k)) c).comp_injective
      (Prod.mk_right_injective x)
  have h1 : HasSum (fun r : P × (∀ k, n k) => star (compose V B r (π, i)) * compose V B r (π', j))
      (gramV V π π' fun k => gramK (a k) (α k) (α' k)) := by
    rw [← hG]; exact hasSum_gram V B hBsq π π' i j
  have hU := hV n B fun k => Matrix.mem_unitaryGroup_iff'.2 (hBB k)
  have h2 := isIsoKernel_of_conjTranspose_mul (Matrix.mem_unitaryGroup_iff'.1 hU) (π, i) (π', j)
  have hval := h1.unique h2
  have hidx : ((π, i) = (π', j)) ↔ ((π, α) = (π', α')) := by
    simp only [Prod.mk.injEq, funext_iff]
    exact and_congr Iff.rfl (forall_congr' fun k => hij k)
  have := hasSum_gram V a hsq π π' α α'
  rwa [hval, if_congr hidx rfl rfl] at this

/-- `(compose V a)ᴴ = compose Vᴴ aᴴ`. -/
theorem compose_conjTranspose {P : Type} [Fintype P] (V : Proc P P) {κ : Fin 3 → Type}
    (a : ∀ k, Matrix (Bool × κ k) (Bool × κ k) ℂ) :
    (compose V a).conjTranspose = compose V.conjTranspose fun k => (a k).conjTranspose := by
  funext r c
  simp only [Matrix.conjTranspose_apply, compose, star_sum, star_mul', star_prod]
  rw [Finset.sum_comm]

theorem IsPure.conjTranspose {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (hV : IsPure V) : IsPure V.conjTranspose := by
  intro n _ _ A hA
  have hA' : ∀ k, (A k).conjTranspose ∈ Matrix.unitaryGroup (Bool × n k) ℂ := fun k =>
    Unitary.star_mem (hA k)
  have := hV n (fun k => (A k).conjTranspose) hA'
  have h2 := compose_conjTranspose V fun k => (A k).conjTranspose
  simp only [Matrix.conjTranspose_conjTranspose] at h2
  rw [← h2]
  exact Unitary.star_mem this

theorem isCoIsoKernel_iff_isIsoKernel_conjTranspose {X Y : Type} [DecidableEq Y]
    (a : Matrix Y X ℂ) : IsCoIsoKernel a ↔ IsIsoKernel a.conjTranspose := by
  simp only [IsCoIsoKernel, IsIsoKernel, Matrix.conjTranspose_apply, star_star]

/-- **Gap (b), unitary form.** -/
theorem isUnitaryKer_of_isPure {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (hV : IsPure V) : IsUnitaryKer V := by
  intro κ _ a hc hr
  refine unitary_of_unitaryKernel _ (isPureKer_of_isPure hV κ a hc) ?_
  rw [isCoIsoKernel_iff_isIsoKernel_conjTranspose, compose_conjTranspose]
  exact isPureKer_of_isPure hV.conjTranspose κ _ fun k =>
    (isCoIsoKernel_iff_isIsoKernel_conjTranspose _).1 (hr k)

/-- **Gap (b) closed: finite purity implies purity against ancillas in arbitrary Hilbert
spaces, for every `V`.** -/
theorem isPureHilbert_of_isPure {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (hV : IsPure V) : IsPureHilbert V :=
  (isUnitaryKer_of_isPure hV).isPureHilbert

theorem IsUnitaryKer.isPure {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsUnitaryKer V) : IsPure V := by
  intro n _ _ A hA
  have hc : ∀ k, IsIsoKernel (A k) := fun k =>
    isIsoKernel_of_conjTranspose_mul (Matrix.mem_unitaryGroup_iff'.1 (hA k))
  have hr : ∀ k, IsCoIsoKernel (A k) := fun k => by
    rw [isCoIsoKernel_iff_isIsoKernel_conjTranspose]
    exact isIsoKernel_of_conjTranspose_mul (by
      rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 (hA k))
  obtain ⟨U, hU⟩ := h n A hc hr
  rw [Matrix.mem_unitaryGroup_iff']
  apply conjTranspose_mul_of_isIsoKernel
  intro c c'
  have h1 := hasSum_inner_lp (U (lp.single 2 c (1 : ℂ))) (U (lp.single 2 c' (1 : ℂ)))
  simp only [hU, LinearIsometryEquiv.inner_map_map, lp.inner_single_left, lp.single_apply,
    Pi.single_apply, RCLike.inner_apply, map_one, mul_one] at h1
  convert h1 using 1

theorem isPure_iff_isUnitaryKer {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) :
    IsPure V ↔ IsUnitaryKer V :=
  ⟨isUnitaryKer_of_isPure, IsUnitaryKer.isPure⟩

theorem isPure_iff_isPureHilbert {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) :
    IsPure V ↔ IsPureHilbert V :=
  (isPure_iff_isUnitaryKer V).trans (isPureHilbert_iff_isUnitaryKer V).symm

theorem isPure_iff_isPureKer {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) :
    IsPure V ↔ IsPureKer V :=
  ⟨isPureKer_of_isPure, IsPureKer.isPure⟩

end PFUL.Counterexample
