/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Appendix F.5: the combinatorial core of the continuous-alphabet theorem

Inputs and outputs of each party are the same abelian group `G k` (any cardinality, e.g. `ℝ`
or the circle). For a process function `w`, closing the loop with local translations
`i ↦ i + e k` has exactly one fixed point; the source-to-fixed-point map is the inverse of
`tau w o = o - w o`. We prove, with no measure theory and no finiteness:

* `tau_bijective` : `tau w` is a bijection;
* `fiber_const` : if `tau w o` and `tau w o'` agree off party `a`, then `w o a = w o' a`
  (the one-party reduction used in the measure-preservation proof of F.5);
* `tauInv_apply` : hence `(tau w)⁻¹ e a = e a + c a e` with `c a e` depending only on the
  coordinates of `e` other than `a` (`c_indep`).

The measure-theoretic step (Fubini on the recursive shear decomposition) is in the paper, F.5.
-/
import PFUL.Countable

namespace PFUL.Continuous

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ k, AddCommGroup (G k)]

/-- `tau w o = o - w o`; the source value `e` for which `o` is the fixed point. -/
def tau (w : (∀ k, G k) → (∀ k, G k)) (o : ∀ k, G k) : ∀ k, G k := o - w o

variable {w : (∀ k, G k) → (∀ k, G k)}

theorem tau_bijective (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) :
    Function.Bijective (tau w) := by
  constructor
  · intro o o' h
    obtain ⟨s, _, hu⟩ := hw (fun k i => i + tau w o k)
    have h1 : ∀ k, w o k + tau w o k = o k := fun k => by simp [tau]
    have h2 : ∀ k, w o' k + tau w o k = o' k := fun k => by rw [h]; simp [tau]
    exact (hu o h1).trans (hu o' h2).symm
  · intro e
    obtain ⟨s, hs, _⟩ := hw (fun k i => i + e k)
    refine ⟨s, funext fun k => ?_⟩
    have := hs k
    simp only [tau, Pi.sub_apply]; rw [← this]; abel

theorem fiber_const (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) (a : ι)
    {o o' : ∀ k, G k} (h : ∀ k, k ≠ a → tau w o k = tau w o' k) : w o a = w o' a := by
  classical
  by_contra hne
  let g : G a → G a := fun x => if x = w o a then o a else o' a
  let f : ∀ k, G k → G k := Function.update (fun k i => i + tau w o k) a g
  obtain ⟨s, _, hu⟩ := hw f
  have h1 : ∀ k, f k (w o k) = o k := by
    intro k
    by_cases hk : k = a
    · subst hk; simp [f, g]
    · simp [f, Function.update_of_ne hk, tau]
  have h2 : ∀ k, f k (w o' k) = o' k := by
    intro k
    by_cases hk : k = a
    · subst hk; simp [f, g, Ne.symm hne]
    · simp only [f, Function.update_of_ne hk]; rw [h k hk]; simp [tau]
  have : o = o' := (hu o h1).trans (hu o' h2).symm
  exact hne (by rw [this])

/-- The inverse of `tau w` (the closed-loop map for translations). -/
noncomputable def tauInv (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) :
    (∀ k, G k) → (∀ k, G k) :=
  Function.surjInv (tau_bijective hw).2

/-- The shear offsets: `c a e = w (tauInv e) a`. -/
noncomputable def c (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) (a : ι)
    (e : ∀ k, G k) : G a :=
  w (tauInv hw e) a

theorem tau_tauInv (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) (e : ∀ k, G k) :
    tau w (tauInv hw e) = e :=
  Function.surjInv_eq _ e

theorem tauInv_apply (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w)
    (e : ∀ k, G k) (a : ι) : tauInv hw e a = e a + c hw a e := by
  have := congrFun (tau_tauInv hw e) a
  simp only [tau, Pi.sub_apply] at this
  simp only [c]; rw [← this]; abel

/-- `c a e` does not depend on `e a`: the offset of party `a` is a function of the other
parties' source values only. -/
theorem c_indep (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) (a : ι)
    {e e' : ∀ k, G k} (h : ∀ k, k ≠ a → e k = e' k) : c hw a e = c hw a e' := by
  apply fiber_const hw a
  intro k hk; rw [tau_tauInv, tau_tauInv]; exact h k hk

end PFUL.Continuous
