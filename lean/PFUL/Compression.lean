/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13: compressing an infinite isometric kernel to a finite unitary

`exists_finite_compression` : let `a : (O × κ) ← (I × κ)` be a kernel with orthonormal columns
(an isometry of `ℓ²`, `κ` of any cardinality), `I ≃ O` finite, and `α, α' ∈ κ`. Then there is a
finite ancilla `n` and a **unitary** matrix `B : (O × n) ← (I × n)` with two indices `i, j ∈ n`
(`i = j ↔ α = α'`) whose cross Gram data at the columns `(·, i)`, `(·, j)` equal those of `a` at
the columns `(·, α)`, `(·, α')`:
`Σ_b conj B (x,b) (y,i) · B (x',b) (y',j) = Σ_b conj a (x,b) (y,α) · a (x',b) (y',α')`.
Construction: coordinates of the finitely many vectors `a (x, ·) (y, α)`, `a (x, ·) (y, α')` in an
orthonormal basis of their (finite-dimensional) span in `ℓ²(κ)`, padded by two extra ancilla
levels, then extended from an orthonormal family to an orthonormal basis
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).
-/
import PFUL.CounterexampleHilbert

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false

namespace PFUL.Counterexample

theorem inner_lp_tsum {R : Type} (f g : L2 R) : ⟪f, g⟫_ℂ = ∑' r, star (f r) * g r :=
  (hasSum_inner_lp f g).tsum_eq.symm

theorem inner_euclid {T : Type} [Fintype T] (f g : EuclideanSpace ℂ T) :
    ⟪f, g⟫_ℂ = ∑ t, star (f t) * g t := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [RCLike.inner_apply]; simp [mul_comm]

/-- A finite square-free version of `Matrix.mul_eq_one_comm`: for `B : (O × n) ← (I × n)` with
`I ≃ O`, `Bᴴ B = 1` implies `B Bᴴ = 1`. -/
theorem mul_conjTranspose_eq_one {I O n : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] [Fintype n] [DecidableEq n] (σ : I ≃ O) {B : Matrix (O × n) (I × n) ℂ}
    (h : B.conjTranspose * B = 1) : B * B.conjTranspose = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.prodCongr σ (Equiv.refl n))).1 h

theorem exists_finite_compression {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (σ : I ≃ O) {κ : Type} [DecidableEq κ] (a : Matrix (O × κ) (I × κ) ℂ)
    (ha : IsIsoKernel a) (α α' : κ) :
    ∃ (n : Type) (_ : Fintype n) (_ : DecidableEq n) (B : Matrix (O × n) (I × n) ℂ) (i j : n),
      B.conjTranspose * B = 1 ∧ B * B.conjTranspose = 1 ∧ (i = j ↔ α = α') ∧
      ∀ x y x' y', HasSum (fun b => star (a (x, b) (y, α)) * a (x', b) (y', α'))
        (∑ b, star (B (x, b) (y, i)) * B (x', b) (y', j)) := by
  classical
  let sel : Bool → κ := fun z => if z then α' else α
  let col : I × Bool → I × κ := fun p => (p.1, sel p.2)
  have hsq : ∀ (c : I × κ) (x : O), Summable fun b : κ => ‖a (x, b) c‖ ^ 2 := fun c x =>
    (summable_sq_of_isIsoKernel ha c).comp_injective (Prod.mk_right_injective x)
  have hmem : ∀ (c : I × κ) (x : O), Memℓp (fun b : κ => a (x, b) c) 2 := by
    intro c x
    refine memℓp_gen ?_
    simpa using hsq c x
  let g : (I × Bool) × O → L2 κ := fun q => ⟨fun b => a (q.2, b) (col q.1), hmem _ _⟩
  let L : Submodule ℂ (L2 κ) := Submodule.span ℂ (Set.range g)
  have : FiniteDimensional ℂ L := FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  let d := Module.finrank ℂ L
  let ob := stdOrthonormalBasis ℂ L
  let crd : (I × Bool) × O → Fin d → ℂ := fun q =>
    ob.repr ⟨g q, Submodule.subset_span ⟨q, rfl⟩⟩
  have hcrd : ∀ q q', ∑ t, star (crd q t) * crd q' t = ∑' b, star (g q b) * g q' b := by
    intro q q'
    rw [← inner_lp_tsum, ← inner_euclid]
    simp only [crd, LinearIsometryEquiv.inner_map_map]
    rfl
  have hcol : ∀ q q' : (I × Bool) × O, col q.1 = col q'.1 → q.2 = q'.2 → crd q = crd q' := by
    intro q q' h1 h2
    have hg : g q = g q' := by
      apply Subtype.ext; funext b
      show a (q.2, b) (col q.1) = a (q'.2, b) (col q'.1)
      rw [h1, h2]
    have hL : (⟨g q, Submodule.subset_span ⟨q, rfl⟩⟩ : L) =
        ⟨g q', Submodule.subset_span ⟨q', rfl⟩⟩ := Subtype.ext hg
    simp only [crd, hL]
  -- the ancilla and the target vectors
  let n := Fin d ⊕ Bool
  let idx : Bool → n := fun z => Sum.inr (if α = α' then false else z)
  let tix : I × Bool → I × n := fun p => (p.1, idx p.2)
  let v' : I × Bool → EuclideanSpace ℂ (O × n) := fun p =>
    WithLp.toLp 2 fun r => Sum.elim (fun t => crd (p, r.1) t) (fun _ => 0) r.2
  let v : I × n → EuclideanSpace ℂ (O × n) := fun c =>
    Sum.elim (fun _ => 0) (fun z => v' (c.1, z)) c.2
  have htix : ∀ p p', tix p = tix p' ↔ col p = col p' := by
    rintro ⟨y, z⟩ ⟨y', z'⟩
    by_cases h : α = α'
    · cases z <;> cases z' <;> simp [tix, idx, col, sel, h]
    · have h' : α' ≠ α := Ne.symm h
      cases z <;> cases z' <;> simp [tix, idx, col, sel, h, h'] <;>
        exact fun _ hh => Bool.noConfusion (Sum.inr_injective hh)
  have hvt : ∀ p, v (tix p) = v' p := by
    rintro ⟨y, z⟩
    by_cases h : α = α'
    · simp only [v, tix, idx, h, if_true, Sum.elim_inr]
      have : ∀ x, crd ((y, false), x) = crd ((y, z), x) := fun x =>
        hcol _ _ (by cases z <;> simp [col, sel, h]) rfl
      simp only [v', this]
    · simp [v, tix, idx, h]
  have hfib : ∀ (c c' : I × κ), HasSum (fun r : O × κ => star (a r c) * a r c')
      (∑ x, ∑' b, star (a (x, b) c) * a (x, b) c') := fun c c' =>
    hasSum_prod_fintype _ _ fun x =>
      (summable_star_mul (hsq c x) (hsq c' x)).of_norm.hasSum
  have hv' : ∀ p p', ⟪v' p, v' p'⟫_ℂ = if col p = col p' then 1 else 0 := by
    intro p p'
    rw [inner_euclid, Fintype.sum_prod_type]
    have : ∀ x, ∑ y : n, star ((v' p) (x, y)) * (v' p') (x, y) =
        ∑' b, star (a (x, b) (col p)) * a (x, b) (col p') := by
      intro x
      rw [Fintype.sum_sum_type]
      simp only [v', PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr, star_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
      rw [hcrd]
    simp only [this]
    exact (hfib (col p) (col p')).unique (ha (col p) (col p'))
  have hon : Orthonormal ℂ ((Set.range tix).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨c, hc⟩ ⟨c', hc'⟩
    obtain ⟨p, rfl⟩ := hc
    obtain ⟨p', rfl⟩ := hc'
    show ⟪v (tix p), v (tix p')⟫_ℂ = _
    rw [hvt, hvt, hv']
    by_cases hh : col p = col p'
    · have : tix p = tix p' := (htix p p').2 hh
      simp only [hh, if_true]
      rw [if_pos (Subtype.ext this)]
    · have : tix p ≠ tix p' := fun e => hh ((htix p p').1 e)
      simp only [hh, if_false]
      rw [if_neg (fun e => this (congrArg Subtype.val e))]
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (O × n)) = Fintype.card (I × n) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod, Fintype.card_congr σ]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  let B : Matrix (O × n) (I × n) ℂ := Matrix.of fun r c => (b c) r
  have hBB : B.conjTranspose * B = 1 := by
    ext c c'
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, B, Matrix.of_apply]
    rw [← inner_euclid, orthonormal_iff_ite.1 b.orthonormal c c', Matrix.one_apply]
  refine ⟨n, inferInstance, inferInstance, B, idx false, idx true, hBB,
    mul_conjTranspose_eq_one σ hBB, ?_, fun x y x' y' => ?_⟩
  · by_cases h : α = α'
    · simp [idx, h]
    · simp only [idx, h, if_false, h, iff_false]
      exact fun hh => Bool.noConfusion (Sum.inr_injective hh)
  · have e1 : b (y, idx false) = v' (y, false) := by
      rw [hb _ ⟨(y, false), rfl⟩]; exact hvt _
    have e2 : b (y', idx true) = v' (y', true) := by
      rw [hb _ ⟨(y', true), rfl⟩]; exact hvt _
    simp only [B, Matrix.of_apply, e1, e2]
    rw [Fintype.sum_sum_type]
    simp only [v', PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    rw [hcrd]
    exact (summable_star_mul (hsq _ x) (hsq _ x')).of_norm.hasSum

end PFUL.Counterexample
