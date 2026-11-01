/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Theorem N.1: the converse without ancillas

With trivial ancillas (`X k = Y k = Unit`) and `|I k| = |O k|`:
the closed loop is unitary for every choice of local unitaries iff `w` is a process function.

* `gram`: row Gram identity `(M Mᴴ)[r,r'] = ∏ₖ Σ_p Vₖ(rₖ, w r k + p) conj Vₖ(r'ₖ, w r' k + p)`.
* `pf_imp_unitary_noAncilla`: (⇐), from `induced_mul_conjTranspose_complex`.
* `exclusivity_of_unitary_noAncilla`: (⇒) to exclusivity, with an explicit witness:
  a permutation at parties where the outputs differ, and a rational Householder reflection
  at parties where the outputs agree but the inputs differ.
* `unitary_noAncilla_iff_pf`: Theorem N.1.
-/
import PFUL.UnitaryLift
import PFUL.ExclusivityCount

open Finset Matrix

set_option linter.unusedSectionVars false

namespace PFUL.NoAncilla

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- **Row Gram identity** (any ancillas). -/
theorem gram (w : (∀ k, O k) → (∀ k, I k)) (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ)
    (r r' : (∀ k, O k) × (∀ k, Y k)) :
    (induced ℂ w V * (induced ℂ w V)ᴴ) r r'
      = ∏ k, ∑ p : I k × X k, V k (r.1 k, r.2 k) (w r.1 k + p.1, p.2)
          * star (V k (r'.1 k, r'.2 k) (w r'.1 k + p.1, p.2)) := by
  rw [Fintype.prod_sum, Matrix.mul_apply]
  simp only [conjTranspose_apply, induced, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι I X).symm _ _ (fun c => rfl))

/-- Lift a square-ish matrix to trivial ancillas. -/
def liftU {A B : Type*} (W : Matrix A B ℂ) : Matrix (A × Unit) (B × Unit) ℂ :=
  fun r c => W r.1 c.1

lemma liftU_unitary {A B : Type*} [Fintype B] [DecidableEq A] (W : Matrix A B ℂ)
    (hW : W * Wᴴ = 1) : liftU W * (liftU W)ᴴ = 1 := by
  ext r r'
  have := congrFun (congrFun hW r.1) r'.1
  simp only [Matrix.mul_apply, conjTranspose_apply, liftU, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton] at this ⊢
  rw [this]
  obtain ⟨a, ⟨⟩⟩ := r; obtain ⟨b, ⟨⟩⟩ := r'
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.one_apply, h]

/-- Gram factor for trivial ancillas. -/
lemma gram_liftU (w : (∀ k, O k) → (∀ k, I k)) (W : ∀ k, Matrix (O k) (I k) ℂ)
    (s s' : ∀ k, O k) :
    (induced ℂ w (fun k => liftU (W k)) * (induced ℂ w (fun k => liftU (W k)))ᴴ)
        (s, fun _ => ()) (s', fun _ => ())
      = ∏ k, ∑ i : I k, W k (s k) (w s k + i) * star (W k (s' k) (w s' k + i)) := by
  rw [gram]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [liftU, Fintype.sum_prod_type]

/-- **Theorem N.1 (⇐)**: process function ⇒ unitary loop, no ancillas. -/
theorem pf_imp_unitary_noAncilla (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Unit) (I k × Unit) ℂ) (hV : ∀ k, V k * (V k)ᴴ = 1)
    (hcard : ∀ k, Fintype.card (I k) = Fintype.card (O k)) :
    induced ℂ w V * (induced ℂ w V)ᴴ = 1 ∧ (induced ℂ w V)ᴴ * induced ℂ w V = 1 :=
  ⟨induced_mul_conjTranspose_complex w hw V hV,
    induced_conjTranspose_mul w hw V hV (fun k => by simp [Fintype.card_prod, hcard k])⟩

/-! ### Explicit witnesses -/

/-- Permutation matrix `W o i = [i = σ o]`. -/
def permW {A B : Type*} (σ : A ≃ B) [DecidableEq B] : Matrix A B ℂ :=
  fun o i => if i = σ o then 1 else 0

lemma permW_unitary {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] (σ : A ≃ B) :
    permW σ * (permW σ)ᴴ = 1 := by
  ext a a'
  simp only [Matrix.mul_apply, conjTranspose_apply, permW]
  by_cases h : a = a'
  · subst h; simp [Matrix.one_apply]
  · have : σ a ≠ σ a' := fun h' => h (σ.injective h')
    simp [Matrix.one_apply, h, this, Ne.symm h]

/-- Real Householder reflection `H = 1 - 2 v vᵀ / ‖v‖²`. -/
noncomputable def house {B : Type*} [Fintype B] [DecidableEq B] (v : B → ℝ) (i j : B) : ℝ :=
  (if i = j then 1 else 0) - 2 * v i * v j / ∑ l, v l ^ 2

lemma house_orth {B : Type*} [Fintype B] [DecidableEq B] (v : B → ℝ) (hN : ∑ l, v l ^ 2 ≠ 0)
    (i k : B) : ∑ j, house v i j * house v k j = if i = k then 1 else 0 := by
  have e : ∀ j, house v i j * house v k j
      = (if i = j then (if k = j then 1 else 0) else 0)
        - 2 * v i * v k / (∑ l, v l ^ 2) * ((if i = j then 1 else 0) + (if k = j then 1 else 0))
        + 4 * v i * v k / (∑ l, v l ^ 2) ^ 2 * v j ^ 2 := by
    intro j
    unfold house
    by_cases h1 : i = j <;> by_cases h2 : k = j
    · subst h1; subst h2; simp; field_simp; ring
    · subst h1; simp [h2]; field_simp; ring
    · subst h2; simp [h1]; field_simp; ring
    · simp [h1, h2]; field_simp; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hik : i = k
  · subst hik; simp; field_simp; ring
  · simp [hik, Ne.symm hik]; field_simp; ring

/-- Householder matrix transported along `e : A ≃ B`. -/
noncomputable def houseW {A B : Type*} [Fintype B] [DecidableEq B] (e : A ≃ B) (v : B → ℝ) :
    Matrix A B ℂ := fun o i => (house v (e o) i : ℂ)

lemma houseW_unitary {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] (e : A ≃ B)
    (v : B → ℝ) (hN : ∑ l, v l ^ 2 ≠ 0) : houseW e v * (houseW e v)ᴴ = 1 := by
  ext a a'
  simp only [Matrix.mul_apply, conjTranspose_apply, houseW, Complex.star_def,
    Complex.conj_ofReal]
  have := house_orth v hN (e a) (e a')
  rw [← Complex.ofReal_inj] at this
  push_cast at this
  rw [this, Matrix.one_apply]
  simp only [e.injective.eq_iff]
  split_ifs <;> simp

/-- The vector `2 e_p + e_q` (`p ≠ q`). -/
def vec2 {B : Type*} [DecidableEq B] (p q : B) (j : B) : ℝ :=
  if j = p then 2 else if j = q then 1 else 0

lemma vec2_norm {B : Type*} [Fintype B] [DecidableEq B] {p q : B} (hpq : p ≠ q) :
    ∑ l, vec2 p q l ^ 2 = 5 := by
  have : ∀ l, vec2 p q l ^ 2 = 4 * (if p = l then 1 else 0) + (if q = l then 1 else 0) := by
    intro l; unfold vec2
    by_cases h1 : l = p
    · subst h1; have : q ≠ l := Ne.symm hpq; simp [this]; (try norm_num)
    · by_cases h2 : l = q
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp; norm_num

lemma house_vec2_row_nonpos {B : Type*} [Fintype B] [DecidableEq B] {p q : B} (hpq : p ≠ q)
    (j : B) : house (vec2 p q) p j ≤ 0 := by
  unfold house
  rw [vec2_norm hpq]
  unfold vec2
  by_cases h1 : j = p
  · subst h1; simp; norm_num
  · by_cases h2 : j = q
    · subst h2; simp [h1, Ne.symm h1]; norm_num
    · simp [h1, h2, Ne.symm h1]

lemma house_vec2_pq {B : Type*} [Fintype B] [DecidableEq B] {p q : B} (hpq : p ≠ q) :
    0 < house (vec2 p q) p q * house (vec2 p q) p p := by
  unfold house
  rw [vec2_norm hpq]
  unfold vec2
  simp [hpq, Ne.symm hpq]; norm_num

/-- **Theorem N.1 (⇒ exclusivity)**, explicit witness: if the loop is unitary for every
tuple of local unitaries without ancillas, then `w` satisfies exclusivity. -/
theorem exclusivity_of_unitary_noAncilla (w : (∀ k, O k) → (∀ k, I k)) (e : ∀ k, O k ≃ I k)
    (h : ∀ V : ∀ k, Matrix (O k × Unit) (I k × Unit) ℂ, (∀ k, V k * (V k)ᴴ = 1) →
      induced ℂ w V * (induced ℂ w V)ᴴ = 1)
    {s s' : ∀ k, O k} (hne : s ≠ s') : ∃ k, s k ≠ s' k ∧ w s k = w s' k := by
  classical
  by_contra hc
  push Not at hc
  -- δ k = w s k - w s' k
  let δ : ∀ k, I k := fun k => w s k - w s' k
  -- choice of W k
  let σ : ∀ k, O k ≃ I k := fun k =>
    (e k).trans (Equiv.swap (e k (s k)) (e k (s' k) + δ k))
  let W : ∀ k, Matrix (O k) (I k) ℂ := fun k =>
    if s k = s' k ∧ δ k ≠ 0 then houseW (e k) (vec2 (e k (s k)) (e k (s k) + δ k))
    else permW (σ k)
  have hW : ∀ k, W k * (W k)ᴴ = 1 := by
    intro k
    by_cases hk : s k = s' k ∧ δ k ≠ 0
    · simp only [W, if_pos hk]
      apply houseW_unitary
      rw [vec2_norm]; · norm_num
      intro h0; exact hk.2 (by have h1 := congrArg (· - e k (s k)) h0; simp at h1; exact h1.symm)
    · simp only [W, if_neg hk]; exact permW_unitary _
  have hU := h (fun k => liftU (W k)) (fun k => liftU_unitary _ (hW k))
  have h0 := congrFun (congrFun hU (s, fun _ => ())) (s', fun _ => ())
  rw [gram_liftU, Matrix.one_apply_ne (by intro h; exact hne (congrArg Prod.fst h))] at h0
  revert h0
  rw [Finset.prod_eq_zero_iff, imp_false]
  push Not
  intro k _
  by_cases hk : s k = s' k ∧ δ k ≠ 0
  · simp only [W, if_pos hk]
    set p := e k (s k)
    have hpq : p ≠ p + δ k := by
      intro h0; exact hk.2 (by have h1 := congrArg (· - p) h0; simp at h1; exact h1.symm)
    -- rewrite as a real sum of nonnegative terms
    have hreal : ∑ i : I k, houseW (e k) (vec2 p (p + δ k)) (s k) (w s k + i)
        * star (houseW (e k) (vec2 p (p + δ k)) (s' k) (w s' k + i))
        = ((∑ i : I k, house (vec2 p (p + δ k)) p (w s k + i)
            * house (vec2 p (p + δ k)) p (w s' k + i) : ℝ) : ℂ) := by
      simp only [houseW, ← hk.1, Complex.star_def, Complex.conj_ofReal]
      push_cast; rfl
    rw [hreal, Complex.ofReal_ne_zero]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg_of_nonpos_of_nonpos (house_vec2_row_nonpos hpq _)
        (house_vec2_row_nonpos hpq _)
    · refine ⟨p - w s' k, Finset.mem_univ _, ?_⟩
      have h1 : w s k + (p - w s' k) = p + δ k := by simp only [δ]; abel
      have h2 : w s' k + (p - w s' k) = p := by abel
      rw [h1, h2]
      exact house_vec2_pq hpq
  · simp only [W, if_neg hk]
    -- σ (s k) - σ (s' k) = δ k
    have hσ : σ k (s k) = e k (s' k) + δ k ∧ σ k (s' k) = e k (s' k) := by
      by_cases hss : s k = s' k
      · have hd : δ k = 0 := by by_contra hd; exact hk ⟨hss, hd⟩
        simp [σ, hss, hd]
      · have hd : δ k ≠ 0 := by
          intro hd; apply hc k hss; simpa [δ, sub_eq_zero] using hd
        have n1 : e k (s' k) ≠ e k (s k) := fun h' => hss ((e k).injective h').symm
        have n2 : e k (s' k) ≠ e k (s' k) + δ k := by
          intro h'; apply hd; have h1 := congrArg (· - e k (s' k)) h'; simp at h1; exact h1.symm
        refine ⟨by simp [σ], ?_⟩
        simp only [σ, Equiv.trans_apply]
        exact Equiv.swap_apply_of_ne_of_ne n1 n2
    rw [Finset.sum_eq_single (e k (s' k) - w s' k)]
    · have h1 : w s k + (e k (s' k) - w s' k) = σ k (s k) := by
        rw [hσ.1]; simp only [δ]; abel
      have h2 : w s' k + (e k (s' k) - w s' k) = σ k (s' k) := by rw [hσ.2]; abel
      simp [permW, h1, h2]
    · intro i _ hi
      have : w s' k + i ≠ σ k (s' k) := by
        rw [hσ.2]; intro h'; apply hi; rw [← h']; abel
      simp [permW, this]
    · simp

/-- Exclusivity bounds the number of fixed points by one. -/
lemma N_le_one (w : (∀ k, O k) → (∀ k, I k))
    (hex : ∀ s s' : ∀ k, O k, s ≠ s' → ∃ k, s k ≠ s' k ∧ w s k = w s' k)
    (f : ∀ k, I k → O k) : ExclusivityCount.N w f ≤ 1 := by
  unfold ExclusivityCount.N
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  obtain ⟨k, hk, hw⟩ := hex a b hab
  exact hk (by rw [← ha k, ← hb k, hw])

/-- **Theorem N.1.** Without ancillas and with `|I k| = |O k|` (witnessed by `e`), the closed
loop is unitary for all local unitaries iff `w` is a process function. -/
theorem unitary_noAncilla_iff_pf (w : (∀ k, O k) → (∀ k, I k)) (e : ∀ k, O k ≃ I k) :
    (∀ V : ∀ k, Matrix (O k × Unit) (I k × Unit) ℂ, (∀ k, V k * (V k)ᴴ = 1) →
      induced ℂ w V * (induced ℂ w V)ᴴ = 1 ∧ (induced ℂ w V)ᴴ * induced ℂ w V = 1)
    ↔ IsProcessFunction w := by
  constructor
  · intro h f
    have hex := fun s s' hss => exclusivity_of_unitary_noAncilla w e (fun V hV => (h V hV).1)
      (s := s) (s' := s') hss
    exact ExclusivityCount.exclusive_imp_existsUnique w (fun _ => 0) (fun k => (e k).symm 0)
      (N_le_one w hex) f
  · intro hw V hV
    exact pf_imp_unitary_noAncilla w hw V hV (fun k => (Fintype.card_congr (e k)).symm)

end PFUL.NoAncilla
