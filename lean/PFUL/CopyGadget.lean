/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Theorem 1.2, (⇒): the copy gadget

If `w` is not a process function, there are local unitaries (with ancillas `X k = O k`, `Y k = I k`)
for which the induced closed loop is not an isometry: the squared norm of column `(0,0)` is the
number of fixed points of the offending intervention, which is `≠ 1`.
-/
import PFUL.UnitaryLift

open Finset Matrix

set_option linter.unusedSectionVars false

namespace PFUL.CopyGadget

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, AddCommGroup (O k)] [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]

/-- The copy bijection `(i, x) ↦ (f i + x, i)`. -/
def copyEquiv {A B : Type*} [AddCommGroup B] (g : A → B) : A × B ≃ B × A where
  toFun c := (g c.1 + c.2, c.1)
  invFun r := (r.2, r.1 - g r.2)
  left_inv c := by simp
  right_inv r := by simp

/-- Permutation matrix of an equivalence, `P r c = [r = e c]`. -/
def permMat {R C : Type*} [DecidableEq R] (e : C ≃ R) : Matrix R C ℂ :=
  fun r c => if r = e c then 1 else 0

lemma permMat_mul_conjTranspose {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R]
    [DecidableEq C] (e : C ≃ R) : permMat e * (permMat e)ᴴ = 1 := by
  ext r r'
  simp only [Matrix.mul_apply, conjTranspose_apply, permMat]
  rw [Fintype.sum_equiv e _ (fun q => (if r = q then (1:ℂ) else 0) * star (if r' = q then 1 else 0))
    (fun c => rfl)]
  by_cases h : r = r'
  · subst h; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

lemma conjTranspose_mul_permMat {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R]
    [DecidableEq C] (e : C ≃ R) : (permMat e)ᴴ * permMat e = 1 := by
  ext c c'
  simp only [Matrix.mul_apply, conjTranspose_apply, permMat]
  by_cases h : c = c'
  · subst h; simp [Matrix.one_apply]
  · have : e c ≠ e c' := fun h' => h (e.injective h')
    simp [Matrix.one_apply, h]
    intro q; exact h q.symm

/-- The copy-gadget local unitary for party `k`. -/
def gadget (f : ∀ k, I k → O k) (k : ι) : Matrix (O k × I k) (I k × O k) ℂ :=
  permMat (copyEquiv (f k))

lemma gadget_unitary (f : ∀ k, I k → O k) (k : ι) :
    gadget f k * (gadget f k)ᴴ = 1 ∧ (gadget f k)ᴴ * gadget f k = 1 :=
  ⟨permMat_mul_conjTranspose _, conjTranspose_mul_permMat _⟩

/-- Column `(0,0)` of the closed loop has squared norm = number of fixed points of `f ∘ w`. -/
theorem colnorm_eq_card (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, I k → O k) :
    ((induced ℂ w (gadget f))ᴴ * induced ℂ w (gadget f)) (0, 0) (0, 0)
      = ((Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k).card : ℂ) := by
  have hM : ∀ r : (∀ k, O k) × (∀ k, I k), induced ℂ w (gadget f) r (0, 0)
      = if (∀ k, f k (w r.1 k) = r.1 k) ∧ r.2 = w r.1 then 1 else 0 := by
    rintro ⟨s, y⟩
    simp only [induced, gadget, permMat, copyEquiv, Equiv.coe_fn_mk, Prod.mk.injEq,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, add_zero]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies]
    constructor
    · intro h; exact ⟨fun k => (h k).1.symm, funext fun k => (h k).2⟩
    · rintro ⟨h1, h2⟩ k; exact ⟨(h1 k).symm, congrFun h2 k⟩
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, hM]
  rw [Fintype.sum_prod_type, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ k, f k (w s k) = s k
  · simp [hs]
  · simp [hs]

/-- **Theorem 1.2 (⇒), copy gadget.** If `w` is not a process function, some tuple of local
unitaries (with ancillas `X k = O k`, `Y k = I k`) makes the induced loop fail `Mᴴ M = 1`. -/
theorem not_isometry_of_not_pf (w : (∀ k, O k) → (∀ k, I k)) (hw : ¬ IsProcessFunction w) :
    ∃ V : ∀ k, Matrix (O k × I k) (I k × O k) ℂ,
      (∀ k, V k * (V k)ᴴ = 1 ∧ (V k)ᴴ * V k = 1) ∧
      (induced ℂ w V)ᴴ * induced ℂ w V ≠ 1 := by
  unfold IsProcessFunction at hw
  push Not at hw
  obtain ⟨f, hf⟩ := hw
  refine ⟨gadget f, gadget_unitary f, fun h => ?_⟩
  have h1 := congrFun (congrFun h (0, 0)) (0, 0)
  rw [colnorm_eq_card, Matrix.one_apply_eq] at h1
  have hc : (Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k).card = 1 := by
    exact_mod_cast h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  apply hf
  refine ⟨a, ?_, fun t ht => ?_⟩
  · have : a ∈ Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k := by simp [ha]
    simpa using this
  · have : t ∈ Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k := by simpa using ht
    simpa [ha] using this

/-- **Theorem 1.2 (both directions, finite alphabets).** -/
theorem unitary_iff_pf (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, Matrix (O k × I k) (I k × O k) ℂ,
      (∀ k, V k * (V k)ᴴ = 1 ∧ (V k)ᴴ * V k = 1) →
        induced ℂ w V * (induced ℂ w V)ᴴ = 1 ∧ (induced ℂ w V)ᴴ * induced ℂ w V = 1)
    ↔ IsProcessFunction w := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨V, hV, hne⟩ := not_isometry_of_not_pf w hw
    exact hne (h V hV).2
  · intro hw V hV
    exact ⟨induced_mul_conjTranspose_complex w hw V (fun k => (hV k).1),
      induced_conjTranspose_mul w hw V (fun k => (hV k).1)
        (fun k => by rw [Fintype.card_prod, Fintype.card_prod, mul_comm])⟩

end PFUL.CopyGadget
