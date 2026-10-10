import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import PFUL.UnitaryLift
import Mathlib.Basic.Complex.BigOperators

/-!
# Column side of the unitary lift, via logical consistency (Appendix F.3)

For a process function `w` and local stochastic interventions `q k i : O k → ℝ` (each a probability vector),
`∑ s, ∏ k, q k (w s k) (s k) = 1`. This is the column-norm identity behind `M† M = 1`; it is proved by
averaging the number of fixed points over random deterministic interventions (no dimension count).
-/

open Finset

namespace PFUL.Column

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}
variable [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]

/-- A process function: every deterministic local intervention has exactly one fixed point
(same definition as `PFUL.IsProcessFunction`, without the group structure on inputs). -/
def IsProcessFunction (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ f : ∀ k, I k → O k, ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k

/-- Marginal of a product measure on functions `I' → O'`: the weight of `{h | h i₀ = a}` is `q i₀ a`. -/
lemma marginal {R : Type*} [CommRing R] {I' O' : Type*} [Fintype I'] [DecidableEq I'] [Fintype O'] [DecidableEq O']
    (q : I' → O' → R) (hq : ∀ i, ∑ o, q i o = 1) (i₀ : I') (a : O') :
    ∑ h : I' → O', (∏ i, q i (h i)) * (if h i₀ = a then 1 else 0) = q i₀ a := by
  have key : ∀ h : I' → O', (∏ i, q i (h i)) * (if h i₀ = a then (1:R) else 0)
      = ∏ i, (q i (h i) * (if i = i₀ then (if h i = a then 1 else 0) else 1)) := by
    intro h
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i₀]
    simp
  simp_rw [key]
  rw [← Fintype.prod_sum (fun i o => q i o * (if i = i₀ then (if o = a then (1:R) else 0) else 1))]
  have : ∀ i, ∑ o, q i o * (if i = i₀ then (if o = a then (1:R) else 0) else 1)
      = if i = i₀ then q i₀ a else 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, hq i]
  simp_rw [this]
  rw [Finset.prod_ite_eq' Finset.univ i₀]
  simp

/-- **Column-norm identity.** For a process function and probability-vector interventions,
`∑ s, ∏ k, q k (w s k) (s k) = 1`. -/
theorem sum_prod_eq_one {R : Type*} [CommRing R] (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (q : ∀ k, I k → O k → R) (hq : ∀ k i, ∑ o, q k i o = 1) :
    ∑ s : (∀ k, O k), ∏ k, q k (w s k) (s k) = 1 := by
  classical
  -- expand each factor as a marginal of the product measure on deterministic interventions
  have h1 : ∀ s : (∀ k, O k), ∏ k, q k (w s k) (s k)
      = ∑ g : (∀ k, I k → O k), ∏ k, ((∏ i, q k i (g k i)) * (if g k (w s k) = s k then 1 else 0)) := by
    intro s
    rw [← Fintype.prod_sum (fun k (h : I k → O k) => (∏ i, q k i (h i)) * (if h (w s k) = s k then (1:R) else 0))]
    exact Finset.prod_congr rfl (fun k _ => (marginal (q k) (hq k) (w s k) (s k)).symm)
  simp_rw [h1]
  rw [Finset.sum_comm]
  -- for each g: exactly one fixed point
  have h2 : ∀ g : (∀ k, I k → O k),
      ∑ s : (∀ k, O k), ∏ k, ((∏ i, q k i (g k i)) * (if g k (w s k) = s k then (1:R) else 0))
      = ∏ k, ∏ i, q k i (g k i) := by
    intro g
    simp_rw [Finset.prod_mul_distrib, Finset.prod_boole]
    obtain ⟨s₀, hs₀, huniq⟩ := hw g
    have : ∀ s : (∀ k, O k), (∀ k ∈ Finset.univ, g k (w s k) = s k) ↔ s = s₀ := by
      intro s; constructor
      · intro h; exact huniq s (fun k => h k (Finset.mem_univ k))
      · rintro rfl; exact fun k _ => hs₀ k
    simp_rw [this, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ s₀]
    simp
  simp_rw [h2]
  rw [← Fintype.prod_sum (fun k (h : I k → O k) => ∏ i, q k i (h i))]
  refine Finset.prod_eq_one (fun k _ => ?_)
  rw [← Fintype.prod_sum (fun i o => q k i o)]
  exact Finset.prod_eq_one (fun i _ => hq k i)

end PFUL.Column

namespace PFUL

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- Unit columns (Appendix F.3): if every local operator has orthonormal columns (`(V k)ᴴ * V k = 1`),
every column of the induced operator has norm one. Proved from logical consistency
(`Column.sum_prod_eq_one`), without any dimension count. -/
theorem induced_colnorm (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV' : ∀ k, (V k)ᴴ * V k = 1)
    (c : (∀ k, I k) × (∀ k, X k)) :
    ((induced ℂ w V)ᴴ * induced ℂ w V) c c = 1 := by
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, induced, star_prod, ← prod_mul_distrib]
  rw [Fintype.sum_prod_type]
  have hy : ∀ s : (∀ k, O k), (∑ y : (∀ k, Y k), ∏ k, star (V k (s k, y k) (w s k + c.1 k, c.2 k)) *
      V k (s k, y k) (w s k + c.1 k, c.2 k))
      = ∏ k, ∑ y' : Y k, star (V k (s k, y') (w s k + c.1 k, c.2 k)) * V k (s k, y') (w s k + c.1 k, c.2 k) :=
    fun s => (Fintype.prod_sum (fun k (y' : Y k) => star (V k (s k, y') (w s k + c.1 k, c.2 k)) *
      V k (s k, y') (w s k + c.1 k, c.2 k))).symm
  simp_rw [hy]
  refine Column.sum_prod_eq_one w hw
    (fun k i o => ∑ y' : Y k, star (V k (o, y') (i + c.1 k, c.2 k)) * V k (o, y') (i + c.1 k, c.2 k)) ?_
  intro k i
  have h := congrFun (congrFun (hV' k) (i + c.1 k, c.2 k)) (i + c.1 k, c.2 k)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [conjTranspose_apply] at h
  rw [← h, ← Fintype.sum_prod_type']

/-- **Unitarity without a dimension count.** For local unitaries, the induced operator satisfies
`Mᴴ * M = 1`: rows are orthonormal (`induced_mul_conjTranspose`, exclusivity) and columns have norm one
(`induced_colnorm`, logical consistency), so the projection `1 - Mᴴ M` has zero diagonal and vanishes. -/
theorem induced_conjTranspose_mul_of_colnorm (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ) (hV : ∀ k, V k * (V k)ᴴ = 1)
    (hV' : ∀ k, (V k)ᴴ * V k = 1) :
    (induced ℂ w V)ᴴ * induced ℂ w V = 1 := by
  set A := induced ℂ w V
  have h1 : A * Aᴴ = 1 := induced_mul_conjTranspose ℂ w hw V hV
  set Q := 1 - Aᴴ * A with hQ
  have hQh : Qᴴ = Q := by
    simp [hQ, conjTranspose_sub, conjTranspose_mul]
  have hQQ : Qᴴ * Q = Q := by
    have hP : (Aᴴ * A) * (Aᴴ * A) = Aᴴ * A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A Aᴴ A, h1, Matrix.one_mul]
    rw [hQh, hQ, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP]
    abel
  have hdiag : ∀ c, Q c c = 0 := by
    intro c; rw [hQ, Matrix.sub_apply, Matrix.one_apply_eq, induced_colnorm w hw V hV' c, sub_self]
  have hQ0 : Q = 0 := by
    ext r c
    have h := congrFun (congrFun hQQ c) c
    rw [hdiag c, Matrix.mul_apply] at h
    simp only [conjTranspose_apply] at h
    have h' := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.zero_re] at h'
    have h'' : ∑ r, Complex.normSq (Q r c) = 0 := by
      rw [← h']; refine Finset.sum_congr rfl (fun r _ => ?_); rw [Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => Complex.normSq_nonneg (Q r c))).1 h'' r
      (Finset.mem_univ r)
    simpa using this
  have : 1 - Aᴴ * A = 0 := hQ0
  exact (sub_eq_zero.1 this).symm

end PFUL

#print axioms PFUL.Column.sum_prod_eq_one
#print axioms PFUL.induced_colnorm
#print axioms PFUL.induced_conjTranspose_mul_of_colnorm
