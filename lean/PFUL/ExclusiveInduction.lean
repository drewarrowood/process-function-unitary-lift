/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Exclusivity implies process function, on arbitrary alphabets (no counting)

Induction on the set of active parties. Fix the outputs of the inactive parties; adding a party
`n`, its "reduced intervention" `g c = f n (w (s c) n)` (with `s c` a fixed point of the smaller
system when `n` outputs `c`) is constant by exclusivity, so `c = g c₀` closes the loop.
No finiteness, countability or group structure on the alphabets is needed; only finitely many
parties and nonempty output alphabets.
-/
import PFUL.FiniteBox

set_option linter.unusedSectionVars false

namespace PFUL.FiniteBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*}
  [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

/-- Partial fixed points: parties in `T` are at a fixed point, the others keep the values `u`. -/
theorem exists_partial_fixed (w : (∀ k, O k) → (∀ k, I k)) (hex : Exclusive w)
    [∀ k, Nonempty (O k)] (f : ∀ k, I k → O k) (T : Finset ι) :
    ∀ u : ∀ k, O k, ∃ s : ∀ k, O k, (∀ k, k ∉ T → s k = u k) ∧ ∀ k ∈ T, f k (w s k) = s k := by
  classical
  induction T using Finset.induction_on with
  | empty => exact fun u => ⟨u, fun _ _ => rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert n T hn ih =>
    intro u
    choose s hs1 hs2 using fun c : O n => ih (Function.update u n c)
    have hsn : ∀ c, s c n = c := fun c => by rw [hs1 c n hn]; simp
    let g : O n → O n := fun c => f n (w (s c) n)
    have hg : ∀ c c', g c = g c' := by
      intro c c'
      by_cases hcc : c = c'
      · rw [hcc]
      have hne : s c ≠ s c' := fun h => hcc (by rw [← hsn c, ← hsn c', h])
      obtain ⟨k, hk, he⟩ := hex _ _ hne
      by_cases hkT : k ∈ T
      · exact absurd (by rw [← hs2 c k hkT, ← hs2 c' k hkT, he]) hk
      by_cases hkn : k = n
      · subst hkn; simp only [g, he]
      · exact absurd (by rw [hs1 c k hkT, hs1 c' k hkT]; simp [hkn]) hk
    let c0 : O n := Classical.arbitrary _
    refine ⟨s (g c0), fun k hk => ?_, fun k hk => ?_⟩
    · have hkn : k ≠ n := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkT : k ∉ T := fun h => hk (Finset.mem_insert_of_mem h)
      rw [hs1 _ k hkT]; simp [hkn]
    · rcases Finset.mem_insert.1 hk with rfl | hkT
      · rw [hsn]; exact hg (g c0) c0
      · exact hs2 _ k hkT

/-- **Exclusivity ⇒ process function**, for finitely many parties and arbitrary nonempty
alphabets (finite, countable, or larger). -/
theorem existsUnique_of_exclusive (w : (∀ k, O k) → (∀ k, I k)) (hex : Exclusive w)
    [∀ k, Nonempty (O k)] (f : ∀ k, I k → O k) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  obtain ⟨s, -, hs⟩ := exists_partial_fixed w hex f Finset.univ (fun _ => Classical.arbitrary _)
  exact ⟨s, fun k => hs k (Finset.mem_univ k), fun t ht =>
    fixed_unique hex f ht (fun k => hs k (Finset.mem_univ k))⟩

end PFUL.FiniteBox
