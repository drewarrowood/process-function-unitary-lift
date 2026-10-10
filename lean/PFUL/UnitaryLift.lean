import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

open Finset Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace PFUL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- A process function: every local intervention has exactly one fixed point. -/
def IsProcessFunction (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ f : ∀ k, I k → O k, ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k

/-- Exclusivity: distinct output strings disagree at a party whose input agrees. -/
theorem exclusivity (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    {s s' : ∀ k, O k} (hne : s ≠ s') : ∃ k, s k ≠ s' k ∧ w s k = w s' k := by
  by_contra h
  push Not at h
  let f : ∀ k, I k → O k := fun k x => if x = w s k then s k else s' k
  obtain ⟨t, -, ht⟩ := hw f
  have h1 : ∀ k, f k (w s k) = s k := fun k => by simp [f]
  have h2 : ∀ k, f k (w s' k) = s' k := by
    intro k
    by_cases hk : w s' k = w s k
    · have := h k
      by_contra hc
      exact (by
        have : s k = s' k := by
          by_contra hne'
          exact absurd hk.symm (this hne')
        simp [f, hk, this] at hc)
    · simp [f, hk]
  exact hne ((ht s h1).trans (ht s' h2).symm)

variable (𝕜 : Type*) [Field 𝕜] [StarRing 𝕜]

/-- The operator induced by closing the source/sink permutation unitary
`U |o,e⟩ = |w o + e, o⟩` with local operators `V k : (O k × Y k) × (I k × X k)`. -/
def induced (w : (∀ k, O k) → (∀ k, I k)) (V : ∀ k, Matrix (O k × Y k) (I k × X k) 𝕜) :
    Matrix ((∀ k, O k) × (∀ k, Y k)) ((∀ k, I k) × (∀ k, X k)) 𝕜 :=
  fun r c => ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)

lemma factor_eq {I' X' R : Type*} [AddCommGroup I'] [Fintype I'] [Fintype X'] [Fintype R]
    (V : Matrix R (I' × X') 𝕜) (c : I') (r r' : R) :
    ∑ p : I' × X', V r (c + p.1, p.2) * star (V r' (c + p.1, p.2)) = (V * Vᴴ) r r' := by
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply]
  exact Fintype.sum_equiv ((Equiv.addLeft c).prodCongr (Equiv.refl _)) _ _ (fun p => rfl)

/-- Main theorem: for every process function and all local co-isometries
(`V k * (V k)ᴴ = 1`, e.g. unitaries) the induced source-to-sink operator `M`
satisfies `M * Mᴴ = 1`. -/
theorem induced_mul_conjTranspose (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) 𝕜) (hV : ∀ k, V k * (V k)ᴴ = 1) :
    induced 𝕜 w V * (induced 𝕜 w V)ᴴ = 1 := by
  ext ⟨s, y⟩ ⟨s', y'⟩
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, induced, star_prod, ← prod_mul_distrib]
  -- reorganise the sum over pairs of strings as a sum over strings of pairs
  have hsum : ∑ c : (∀ k, I k) × (∀ k, X k),
      ∏ k, V k (s k, y k) (w s k + c.1 k, c.2 k) * star (V k (s' k, y' k) (w s' k + c.1 k, c.2 k))
      = ∑ p : ∀ k, I k × X k,
      ∏ k, V k (s k, y k) (w s k + (p k).1, (p k).2) *
        star (V k (s' k, y' k) (w s' k + (p k).1, (p k).2)) :=
    Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ (fun c => rfl)
  rw [hsum, ← Fintype.prod_sum (fun k (p : I k × X k) =>
    V k (s k, y k) (w s k + p.1, p.2) * star (V k (s' k, y' k) (w s' k + p.1, p.2)))]
  by_cases hs : s = s'
  · subst hs
    have hk : ∀ k, (∑ p : I k × X k, V k (s k, y k) (w s k + p.1, p.2) *
        star (V k (s k, y' k) (w s k + p.1, p.2))) = if y k = y' k then 1 else 0 := by
      intro k
      rw [factor_eq 𝕜 (V k) (w s k), hV k, Matrix.one_apply]
      simp
    simp only [hk]
    by_cases hy : y = y'
    · subst hy; simp
    · obtain ⟨k, hk'⟩ : ∃ k, y k ≠ y' k := by
        by_contra h; push Not at h; exact hy (funext h)
      rw [Matrix.one_apply, if_neg (by simp [hy])]
      exact prod_eq_zero (mem_univ k) (by simp [hk'])
  · obtain ⟨k, hsk, hwk⟩ := exclusivity w hw hs
    rw [Matrix.one_apply, if_neg (by simp [hs])]
    apply prod_eq_zero (mem_univ k)
    rw [hwk, factor_eq 𝕜 (V k) (w s' k), hV k, Matrix.one_apply, if_neg (by simp [hsk])]

/-- The complex case: closing the lift with arbitrary local unitaries (with local ancillas)
gives an operator with orthonormal rows. When `∏|I k||X k| = ∏|O k||Y k|` it is square, hence unitary. -/
theorem induced_mul_conjTranspose_complex (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV : ∀ k, V k * (V k)ᴴ = 1) :
    induced ℂ w V * (induced ℂ w V)ᴴ = 1 :=
  induced_mul_conjTranspose ℂ w hw V hV

end PFUL

namespace PFUL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- The paper's dimension count: if each local operator is square
(`|I k||X k| = |O k||Y k|`), the induced operator is square. -/
lemma card_eq (hcard : ∀ k, Fintype.card (I k × X k) = Fintype.card (O k × Y k)) :
    Fintype.card ((∀ k, O k) × (∀ k, Y k)) = Fintype.card ((∀ k, I k) × (∀ k, X k)) := by
  simp only [Fintype.card_prod, Fintype.card_pi] at hcard ⊢
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun k _ => (hcard k).symm)

/-- Complex case: after identifying source⊗ancilla with sink⊗ancilla by any bijection `e`
(which exists by `card_eq`), the induced operator lies in the unitary group. -/
theorem induced_unitary (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV : ∀ k, V k * (V k)ᴴ = 1)
    (hcard : ∀ k, Fintype.card (I k × X k) = Fintype.card (O k × Y k))
    (e : ((∀ k, O k) × (∀ k, Y k)) ≃ ((∀ k, I k) × (∀ k, X k))) :
    (induced ℂ w V).submatrix id e ∈ Matrix.unitaryGroup ((∀ k, O k) × (∀ k, Y k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, induced_mul_conjTranspose ℂ w hw V hV]
  exact Matrix.submatrix_one_equiv (Equiv.refl _)

/-- Two-sided unitarity in the complex case: `Mᴴ * M = 1`, using the dimension count `card_eq`
(the paper's Appendix B) and `M * Mᴴ = 1`. -/
theorem induced_conjTranspose_mul (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV : ∀ k, V k * (V k)ᴴ = 1)
    (hcard : ∀ k, Fintype.card (I k × X k) = Fintype.card (O k × Y k)) :
    (induced ℂ w V)ᴴ * induced ℂ w V = 1 := by
  let e := Fintype.equivOfCardEq (card_eq hcard)
  have hu := (Matrix.mem_unitaryGroup_iff'.mp (induced_unitary w hw V hV hcard e))
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id] at hu
  ext i j
  have := congrFun (congrFun hu (e.symm i)) (e.symm j)
  simpa [Matrix.one_apply] using this
