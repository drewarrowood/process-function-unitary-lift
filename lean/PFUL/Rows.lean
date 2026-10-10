import PFUL.Countable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Countable alphabets: factorisation of sums over finite products, and orthonormal rows
-/

open MeasureTheory

namespace PFUL.Countable

/-- **Factorisation lemma.** For finitely many countable types and absolutely summable complex
families, the sum over the product of the product equals the product of the sums. -/
theorem hasSum_pi_prod {K : Type*} [Fintype K] {X : K → Type*} [∀ k, Countable (X k)]
    (g : ∀ k, X k → ℂ) (hg : ∀ k, Summable fun x => ‖g k x‖) :
    HasSum (fun x : (∀ k, X k) => ∏ k, g k (x k)) (∏ k, ∑' x, g k x) := by
  classical
  letI : ∀ k, MeasurableSpace (X k) := fun _ => ⊤
  haveI : ∀ k, MeasurableSingletonClass (X k) := fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hpi : Measure.pi (fun k => (Measure.count : Measure (X k))) = Measure.count := by
    rw [Measure.ext_iff_singleton]
    intro x
    rw [Measure.count_singleton, ← Set.univ_pi_singleton, Measure.pi_pi]
    simp
  have hint : ∀ k, Integrable (g k) Measure.count := fun k => integrable_count_iff.2 (hg k)
  have hI := Integrable.fintype_prod_dep (μ := fun k => (Measure.count : Measure (X k))) hint
  rw [hpi] at hI
  have hS : Summable (fun x : (∀ k, X k) => ‖∏ k, g k (x k)‖) := integrable_count_iff.1 hI
  have h1 := integral_fintype_prod_eq_prod (μ := fun k => (Measure.count : Measure (X k))) g
  rw [hpi, integral_countable hI] at h1
  simp_rw [integral_countable (hint _), count_real_singleton, one_smul] at h1
  rw [← h1]
  exact hS.of_norm.hasSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}

/-- Exclusivity for arbitrary alphabets (same proof as `PFUL.exclusivity`). -/
theorem exclusivity (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    {s s' : ∀ k, O k} (hne : s ≠ s') : ∃ k, s k ≠ s' k ∧ w s k = w s' k := by
  classical
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

lemma shift_summable {I' X' : Type*} [AddCommGroup I'] (v : I' × X' → ℂ)
    (hv : Summable fun c => ‖v c‖ ^ 2) (i : I') :
    Summable fun p : I' × X' => ‖v (i + p.1, p.2)‖ ^ 2 :=
  (((Equiv.addLeft i).prodCongr (Equiv.refl X')).summable_iff (f := fun c => ‖v c‖ ^ 2)).2 hv

lemma shift_hasSum {I' X' : Type*} [AddCommGroup I'] (v u : I' × X' → ℂ) (a : ℂ)
    (h : HasSum (fun c => v c * star (u c)) a) (i : I') :
    HasSum (fun p : I' × X' => v (i + p.1, p.2) * star (u (i + p.1, p.2))) a :=
  (((Equiv.addLeft i).prodCongr (Equiv.refl X')).hasSum_iff (f := fun c => v c * star (u c))).2 h

lemma norm_mul_star_le (a b : ℂ) : ‖a * star b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- **Orthonormal rows, countable alphabets.** If each local kernel `V k` has square-summable,
orthonormal rows, the rows of the induced map are orthonormal:
`∑' (e,x), M r (e,x) * conj (M r' (e,x)) = δ r r'` (as a `HasSum`, so the series converges). -/
theorem induced_rows {X Y : ι → Type*} [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)]
    [∀ k, Countable (X k)] [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (r r' : (∀ k, O k) × (∀ k, Y k)) :
    HasSum (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (w r'.1 k + c.1 k, c.2 k)))
      (if r = r' then 1 else 0) := by
  classical
  let g : ∀ k, I k × X k → ℂ := fun k p =>
    V k (r.1 k, r.2 k) (w r.1 k + p.1, p.2) * star (V k (r'.1 k, r'.2 k) (w r'.1 k + p.1, p.2))
  have hg : ∀ k, Summable fun p => ‖g k p‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_star_le _ _)
      ((shift_summable _ (hsq k _) _).add (shift_summable _ (hsq k _) _))
  have hp := hasSum_pi_prod g hg
  let e : ((∀ k, I k) × (∀ k, X k)) ≃ (∀ k, I k × X k) :=
    { toFun := fun c k => (c.1 k, c.2 k)
      invFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  have hp' := (e.hasSum_iff (f := fun x : (∀ k, I k × X k) => ∏ k, g k (x k))).2 hp
  have hfun : (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (w r'.1 k + c.1 k, c.2 k)))
      = (fun x : (∀ k, I k × X k) => ∏ k, g k (x k)) ∘ e := by
    funext c
    simp only [Function.comp, star_prod, ← Finset.prod_mul_distrib, g, e, Equiv.coe_fn_mk]
  rw [hfun]
  convert hp' using 1
  -- evaluate the product of the factor sums
  have hfac : ∀ k, w r.1 k = w r'.1 k →
      ∑' p, g k p = if (r.1 k, r.2 k) = (r'.1 k, r'.2 k) then 1 else 0 := by
    intro k hk
    have := shift_hasSum (V k (r.1 k, r.2 k)) (V k (r'.1 k, r'.2 k)) _
      (hrow k (r.1 k, r.2 k) (r'.1 k, r'.2 k)) (w r.1 k)
    simp only [g, ← hk]
    exact this.tsum_eq
  by_cases hrr : r = r'
  · subst hrr
    rw [if_pos rfl]
    symm
    exact Finset.prod_eq_one (fun k _ => by rw [hfac k rfl, if_pos rfl])
  · rw [if_neg hrr]
    symm
    by_cases h1 : r.1 = r'.1
    · have h2 : r.2 ≠ r'.2 := fun h2 => hrr (Prod.ext h1 h2)
      obtain ⟨k, hk⟩ : ∃ k, r.2 k ≠ r'.2 k := by
        by_contra h; push Not at h; exact h2 (funext h)
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hfac k (by rw [h1]), if_neg (fun h => hk (congrArg Prod.snd h))]
    · obtain ⟨k, hsk, hwk⟩ := exclusivity w hw h1
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hfac k hwk, if_neg (fun h => hsk (congrArg Prod.fst h))]

end PFUL.Countable

#print axioms PFUL.Countable.hasSum_pi_prod
#print axioms PFUL.Countable.induced_rows
