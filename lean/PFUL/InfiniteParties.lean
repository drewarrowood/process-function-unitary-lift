/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Infinitely many parties: a reduction

For an arbitrary (possibly infinite) index type `ι`, an exclusive non-process function exists
on output alphabets `O` (with some input alphabets) iff there is a fixed-point-free exclusive
self-map `F` of `∀ k, O k`. Uniqueness of fixed points from exclusivity holds for every `ι`.
-/
import Mathlib

universe u

namespace PFUL.Infinite

variable {ι : Type*} {I O : ι → Type*}

def Exclusive (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ s s' : ∀ k, O k, s ≠ s' → ∃ k, s k ≠ s' k ∧ w s k = w s' k

def IsProcessFunction (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ f : ∀ k, I k → O k, ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k

theorem fixed_unique {w : (∀ k, O k) → (∀ k, I k)} (hex : Exclusive w) (f : ∀ k, I k → O k)
    {s s' : ∀ k, O k} (hs : ∀ k, f k (w s k) = s k) (hs' : ∀ k, f k (w s' k) = s' k) :
    s = s' := by
  by_contra hne
  obtain ⟨k, hk, hw⟩ := hex s s' hne
  exact hk (by rw [← hs k, ← hs' k, hw])

/-- Reduction: exclusive non-PF maps exist iff fixed-point-free exclusive self-maps exist. -/

theorem exists_exclusive_not_pf_iff (O : ι → Type u) :
    (∃ (I : ι → Type u) (w : (∀ k, O k) → (∀ k, I k)), Exclusive w ∧ ¬ IsProcessFunction w) ↔
    ∃ F : (∀ k, O k) → (∀ k, O k), (∀ s, F s ≠ s) ∧ Exclusive F := by
  constructor
  · rintro ⟨I, w, hex, hpf⟩
    unfold IsProcessFunction at hpf
    push_neg at hpf
    obtain ⟨f, hf⟩ := hpf
    have hf' : ¬ ∃ s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
      rintro ⟨s, hs⟩
      exact hf ⟨s, hs, fun t ht => fixed_unique hex f ht hs⟩
    refine ⟨fun s k => f k (w s k), ?_, ?_⟩
    · intro s hs
      have hs' : ∀ k, f k (w s k) = s k := fun k => congrFun hs k
      exact hf' ⟨s, hs'⟩
    · intro s s' hne
      obtain ⟨k, hk, hw⟩ := hex s s' hne
      exact ⟨k, hk, by simp only [hw]⟩
  · rintro ⟨F, hF, hex⟩
    refine ⟨O, F, hex, fun h => ?_⟩
    obtain ⟨s, hs, -⟩ := h (fun _ => id)
    exact hF s (funext hs)

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_exclusive_not_pf_iff
