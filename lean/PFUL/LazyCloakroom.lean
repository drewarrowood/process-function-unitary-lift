/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# The lazy cloakroom: freeness of σ cannot be dropped from `unitary_l2_iff_pf_σ`

With the lazy family `σ k a = id` (not free), the closed loop no longer depends on `w`, so it is
unitary for every local kernel whatever `w` is; in particular for a `w` that is not a process
function.
-/
import PFUL.BijectionLaw

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PFUL.General
open PFUL.Countable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*}

/-- The lazy cloakroom: no attendant moves anything. -/
def lazyσ : ∀ k, I k → Equiv.Perm (I k) := fun _ _ => Equiv.refl _

lemma not_free_lazy {B : Type*} [Nontrivial B] : ¬ Free (fun _ : B => Equiv.refl B) := by
  intro h
  obtain ⟨a, a', hne⟩ := exists_pair_ne B
  exact hne (h a a' a rfl)

omit [DecidableEq ι] in
lemma isProcessFunction_const (i : ∀ k, I k) :
    IsProcessFunction (fun _ : (∀ k, O k) => i) :=
  fun f => ⟨fun k => f k (i k), fun _ => rfl, fun _ hs => funext fun k => (hs k).symm⟩

/-- **Lazy cloakroom.** With `σ = lazyσ`, every `w` passes every unitarity test. -/
theorem lazy_unitary_all [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]
    [∀ k, Nonempty (I k)] (w : (∀ k, O k) → (∀ k, I k)) :
    ∀ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (lazyσ k (w r.1 k) (c.1 k), c.2 k) := by
  intro V h1 h2 h3
  obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2_σ lazyσ (fun _ => fun k => Classical.arbitrary (I k))
    (isProcessFunction_const _) V h1 h2 h3
  exact ⟨Φ, fun r c => by rw [hΦ]; rfl⟩

/-- **The converse fails without freeness.** One binary party, `w = id` (not a process function:
the intervention "flip" has no fixed point), yet the lazy loop is unitary for every kernel. -/
theorem lazy_converse_fails :
    ∃ w : (Unit → Bool) → (Unit → Bool),
      ¬ IsProcessFunction w ∧
      ∀ V : ∀ _ : Unit, Bool × Bool → Bool × Bool → ℂ,
        (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
        (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
        (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) →
        ∃ Φ : lp (fun _ : (Unit → Bool) × (Unit → Bool) => ℂ) 2 ≃ₗᵢ[ℂ]
            lp (fun _ : (Unit → Bool) × (Unit → Bool) => ℂ) 2,
          ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
            = ∏ k, V k (r.1 k, r.2 k) (lazyσ (I := fun _ : Unit => Bool) k (w r.1 k) (c.1 k), c.2 k) := by
  refine ⟨id, fun h => ?_, lazy_unitary_all (I := fun _ => Bool) (O := fun _ => Bool) id⟩
  obtain ⟨s, hs, -⟩ := h fun _ b => !b
  have := hs (); simp at this

end PFUL.General

#print axioms PFUL.General.lazy_unitary_all
#print axioms PFUL.General.lazy_converse_fails
#print axioms PFUL.General.not_free_lazy
