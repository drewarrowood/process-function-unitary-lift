import PFUL.Column
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

/-!
# Isometric local maps (Stinespring isometries)

Generalised column identity: if `∑ o, q k i o = λ k` for every `i` (a constant per party), then
`∑ s, ∏ k, q k (w s k) (s k) = ∏ k, λ k` (over ℂ). From it: if every local map is an isometry
(`(V k)ᴴ * V k = 1`, not necessarily square), the induced map is an isometry, `Mᴴ * M = 1`.
-/

open Finset Matrix Polynomial

namespace PFUL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}
variable [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]

theorem Column.sum_prod_eq_prod (w : (∀ k, O k) → (∀ k, I k)) (hw : Column.IsProcessFunction w)
    [∀ k, Nonempty (I k)]
    (q : ∀ k, I k → O k → ℂ) (lam : ι → ℂ) (hq : ∀ k i, ∑ o, q k i o = lam k) :
    ∑ s : (∀ k, O k), ∏ k, q k (w s k) (s k) = ∏ k, lam k := by
  classical
  by_cases hne : ∀ k, Nonempty (O k)
  · let o0 : ∀ k, O k := fun k => (hne k).some
    let P : ℂ[X] := ∑ s : (∀ k, O k), ∏ k, (C (q k (w s k) (s k)) + X * C (if s k = o0 k then 1 else 0))
    let Q : ℂ[X] := ∏ k, (C (lam k) + X)
    have hev : ∀ t : ℂ, (∀ k, lam k + t ≠ 0) → P.eval t = Q.eval t := by
      intro t ht
      simp only [P, Q, eval_finsetSum, eval_prod, eval_add, eval_mul, eval_C, eval_X]
      have h1 := Column.sum_prod_eq_one w hw
        (fun k i o => (q k i o + t * (if o = o0 k then 1 else 0)) / (lam k + t)) (by
          intro k i
          rw [← Finset.sum_div, Finset.sum_add_distrib, hq k i, ← Finset.mul_sum,
            Finset.sum_ite_eq' Finset.univ (o0 k)]
          simp only [Finset.mem_univ, ite_true, mul_one]
          exact div_self (ht k))
      simp only [Finset.prod_div_distrib] at h1
      have hQ : ∏ k, (lam k + t) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun k _ => ht k)
      rw [← Finset.sum_div, div_eq_one_iff_eq hQ] at h1
      exact h1
    haveI : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
    have hPQ : P = Q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hfin : (Set.range (fun k => -lam k)).Finite := Set.finite_range _
      refine ((Set.infinite_univ (α := ℂ)).sdiff hfin).mono ?_
      intro t ht
      refine hev t (fun k h => ht.2 ⟨k, ?_⟩)
      simp only; linear_combination -h
    have := congrArg (Polynomial.eval 0) hPQ
    simp only [P, Q, eval_finsetSum, eval_prod, eval_add, eval_mul, eval_C, eval_X, zero_mul,
      add_zero] at this
    exact this
  · push Not at hne
    obtain ⟨k, hk⟩ := hne
    haveI : IsEmpty (∀ k, O k) := ⟨fun s => hk.false (s k)⟩
    have h0 : lam k = 0 := by
      rw [← hq k (Classical.arbitrary _)]; exact Finset.sum_of_isEmpty _
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact (Finset.prod_eq_zero (Finset.mem_univ k) h0).symm

variable {X Y : ι → Type*}
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- **Isometric local maps give an isometric induced map.** If every local map
`V k : I k × X k → O k × Y k` is an isometry (`(V k)ᴴ * V k = 1`; e.g. a Stinespring isometry,
not necessarily square), then `Mᴴ * M = 1`. -/
theorem induced_isometry [∀ k, AddCommGroup (I k)] (w : (∀ k, O k) → (∀ k, I k))
    (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV' : ∀ k, (V k)ᴴ * V k = 1) :
    (induced ℂ w V)ᴴ * induced ℂ w V = 1 := by
  classical
  ext c c'
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, induced, star_prod, ← prod_mul_distrib]
  rw [Fintype.sum_prod_type]
  have hy : ∀ s : (∀ k, O k), (∑ y : (∀ k, Y k), ∏ k, star (V k (s k, y k) (w s k + c.1 k, c.2 k)) *
      V k (s k, y k) (w s k + c'.1 k, c'.2 k))
      = ∏ k, ∑ y' : Y k, star (V k (s k, y') (w s k + c.1 k, c.2 k)) * V k (s k, y') (w s k + c'.1 k, c'.2 k) :=
    fun s => (Fintype.prod_sum (fun k (y' : Y k) => star (V k (s k, y') (w s k + c.1 k, c.2 k)) *
      V k (s k, y') (w s k + c'.1 k, c'.2 k))).symm
  simp_rw [hy]
  rw [Column.sum_prod_eq_prod w hw
    (fun k i o => ∑ y' : Y k, star (V k (o, y') (i + c.1 k, c.2 k)) * V k (o, y') (i + c'.1 k, c'.2 k))
    (fun k => if (c.1 k, c.2 k) = (c'.1 k, c'.2 k) then 1 else 0) ?_]
  · rw [Finset.prod_boole, Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · intro h
      exact Prod.ext (funext fun k => congrArg Prod.fst (h k (Finset.mem_univ k)))
        (funext fun k => congrArg Prod.snd (h k (Finset.mem_univ k)))
    · rintro rfl; intro k _; rfl
  · intro k i
    have h := congrFun (congrFun (hV' k) (i + c.1 k, c.2 k)) (i + c'.1 k, c'.2 k)
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [conjTranspose_apply] at h
    rw [← Fintype.sum_prod_type', h]
    congr 1
    apply propext
    constructor
    · intro h
      rw [Prod.ext_iff] at h ⊢
      exact ⟨add_left_cancel h.1, h.2⟩
    · intro h
      rw [Prod.ext_iff] at h ⊢
      exact ⟨by simp only at h ⊢; rw [h.1], h.2⟩

end PFUL

#print axioms PFUL.Column.sum_prod_eq_prod
#print axioms PFUL.induced_isometry
