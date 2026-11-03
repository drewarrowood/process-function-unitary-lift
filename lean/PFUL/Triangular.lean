/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Triangular ("Yablo-type") maps: party `k` reads only later parties

* `Triangular F`: `F s k` depends only on `s` restricted to `(k, ∞)`.
* `exists_fixed_of_eventually_good`: if some `s` is consistent at all coordinates `≥ n`, a
  fixed point exists (repair the bad coordinates from the top down). Hence a fixed-point-free
  triangular map is inconsistent at infinitely many coordinates of every history
  (`infinite_bad_of_fixedPointFree`).
* `triangular_witness_of_finite_diff`: for triangular maps, histories that differ in finitely
  many coordinates always have an exclusivity witness (the largest differing coordinate), so
  exclusivity only constrains infinitely-differing pairs.
* `witness_good_bad`: for any exclusive binary `F`, a witness is consistent for exactly one of
  the two histories.
-/
import PFUL.InfiniteParties
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

namespace PFUL.Infinite

/-- Party `k` reads only parties `j > k`. -/
def Triangular (F : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  ∀ s t k, (∀ j, k < j → s j = t j) → F s k = F t k

theorem exists_fixed_of_eventually_good {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Triangular F) :
    ∀ n s, (∀ k, n ≤ k → F s k = s k) → ∃ x, F x = x := by
  intro n
  induction n with
  | zero => exact fun s hs => ⟨s, funext fun k => hs k (Nat.zero_le k)⟩
  | succ n ih =>
    intro s hs
    refine ih (Function.update s n (F s n)) fun k hk => ?_
    have htail : F (Function.update s n (F s n)) k = F s k :=
      hF _ _ k fun j hj => by rw [Function.update_of_ne (by omega)]
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · rw [htail, Function.update_self]
    · rw [htail, Function.update_of_ne (by omega), hs k hlt]

theorem infinite_bad_of_fixedPointFree {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Triangular F)
    (hfree : ∀ s, F s ≠ s) (s : ℕ → Bool) : {k | F s k ≠ s k}.Infinite := by
  intro hfin
  obtain ⟨n, hn⟩ := hfin.bddAbove
  obtain ⟨x, hx⟩ := exists_fixed_of_eventually_good hF (n + 1) s fun k hk => by
    by_contra h; have := hn h; omega
  exact hfree x hx

theorem triangular_witness_of_finite_diff {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Triangular F)
    {s t : ℕ → Bool} (hne : s ≠ t) (hfin : {k | s k ≠ t k}.Finite) :
    ∃ k, s k ≠ t k ∧ F s k = F t k := by
  classical
  have hnon : (hfin.toFinset).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    exact ⟨k, by simpa using hk⟩
  refine ⟨hfin.toFinset.max' hnon, by simpa using hfin.toFinset.max'_mem hnon, hF _ _ _ ?_⟩
  intro j hj
  by_contra h
  have : j ≤ hfin.toFinset.max' hnon := hfin.toFinset.le_max' j (by simpa using h)
  omega

/-- For exclusive binary `F`, every witness is consistent for exactly one of the two histories. -/
theorem witness_good_bad {ι : Type*} {F : (ι → Bool) → (ι → Bool)} {s t : ι → Bool} {k : ι}
    (hk : s k ≠ t k) (hF : F s k = F t k) : (F s k = s k ↔ F t k ≠ t k) := by
  cases h1 : s k <;> cases h2 : t k <;> cases h3 : F s k <;> simp_all

/-- Repair the first `n` coordinates from the top down, keeping the tail. -/
theorem exists_good_below {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Triangular F) :
    ∀ n (s : ℕ → Bool), ∃ x, (∀ k, k < n → F x k = x k) ∧ ∀ k, n ≤ k → x k = s k := by
  intro n
  induction n with
  | zero => exact fun s => ⟨s, fun k hk => absurd hk (Nat.not_lt_zero k), fun _ _ => rfl⟩
  | succ n ih =>
    intro s
    obtain ⟨x, hx, hxs⟩ := ih (Function.update s n (F s n))
    refine ⟨x, fun k hk => ?_, fun k hk => by rw [hxs k (by omega), Function.update_of_ne (by omega)]⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
    · exact hx k hlt
    · rw [hxs k le_rfl, Function.update_self]
      exact hF _ _ _ fun j hj => by rw [hxs j (by omega), Function.update_of_ne (by omega)]

/-- **Continuous triangular maps always have a fixed point** (no exclusivity needed). So a
fixed-point-free triangular map, such as Yablo's, is necessarily discontinuous. -/
theorem exists_fixed_of_triangular_continuous {F : (ℕ → Bool) → (ℕ → Bool)} (hF : Triangular F)
    (hc : ∀ k, Continuous fun s => F s k) : ∃ x, F x = x := by
  classical
  let C : ℕ → Set (ℕ → Bool) := fun n => {x | ∀ k, k < n → F x k = x k}
  have hC : ∀ n, IsClosed (C n) := fun n => by
    simp only [C, Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_eq (hc k) (continuous_apply k)
  have hmono : ∀ n, C (n + 1) ⊆ C n := fun n x hx k hk => hx k (by omega)
  have hne : ∀ n, (C n).Nonempty := fun n =>
    let ⟨x, hx, _⟩ := exists_good_below hF n (fun _ => false); ⟨x, hx⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hne
    (hC 0).isCompact hC
  exact ⟨x, funext fun k => (Set.mem_iInter.1 hx (k + 1)) k (by omega)⟩

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_fixed_of_eventually_good
#print axioms PFUL.Infinite.infinite_bad_of_fixedPointFree
#print axioms PFUL.Infinite.triangular_witness_of_finite_diff
#print axioms PFUL.Infinite.witness_good_bad
#print axioms PFUL.Infinite.exists_fixed_of_triangular_continuous
