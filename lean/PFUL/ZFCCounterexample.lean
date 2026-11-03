/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# A ZFC counterexample: exclusive ⇏ PF for countably many binary parties

No extra set-theoretic hypothesis (cf. `PFUL.CovMCounterexample`, which assumed cov(M) = 𝔠).
Explicit, Borel map `F : (ℕ → Bool) → (ℕ → Bool)`:
* if `s` has infinitely many `true`s, `F s = 0` (all `false`);
* if `s` has finite support, `F s = e₀ ⊕ shiftRight s`, i.e. `F s 0 = true`, `F s (k+1) = s k`.
`F` has no fixed point and is exclusive.
-/
import PFUL.InfiniteParties

open Set

namespace PFUL.Infinite

/-- Finite support. -/
def FinSupp (s : ℕ → Bool) : Prop := {k | s k = true}.Finite

open Classical in
/-- The explicit counterexample. -/
noncomputable def zfcF (s : ℕ → Bool) : ℕ → Bool :=
  if FinSupp s then fun k => match k with | 0 => true | k + 1 => s k else fun _ => false

lemma zfcF_fin {s : ℕ → Bool} (h : FinSupp s) (k : ℕ) :
    zfcF s k = match k with | 0 => true | k + 1 => s k := by simp [zfcF, h]

lemma zfcF_inf {s : ℕ → Bool} (h : ¬ FinSupp s) (k : ℕ) : zfcF s k = false := by
  simp [zfcF, h]

/-- Above a bound of a finite support everything is `false`. -/
lemma bound_of_finSupp {s : ℕ → Bool} (h : FinSupp s) : ∃ N, ∀ k, N ≤ k → s k = false := by
  obtain ⟨N, hN⟩ := h.bddAbove
  refine ⟨N + 1, fun k hk => ?_⟩
  by_contra hc
  have := hN (show k ∈ {k | s k = true} by simpa using hc); omega

lemma exists_true_ge {s : ℕ → Bool} (h : ¬ FinSupp s) (N : ℕ) : ∃ k, N ≤ k ∧ s k = true := by
  by_contra hc; push_neg at hc
  refine h ((finite_lt_nat N).subset fun k hk => ?_)
  by_contra hk'; simp only [mem_setOf_eq, not_lt] at hk hk'; simp [hc k hk'] at hk

lemma cross {s s' : ℕ → Bool} (hs : ¬ FinSupp s) (hs' : FinSupp s') :
    ∃ k, s k ≠ s' k ∧ zfcF s k = zfcF s' k := by
  obtain ⟨N, hN⟩ := bound_of_finSupp hs'
  obtain ⟨k, hk, hsk⟩ := exists_true_ge hs (N + 1)
  refine ⟨k, by rw [hsk, hN k (by omega)]; simp, ?_⟩
  rw [zfcF_inf hs, zfcF_fin hs']
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hN j (by omega)).symm

theorem zfcF_ne (s : ℕ → Bool) : zfcF s ≠ s := by
  intro h
  by_cases hs : FinSupp s
  · have hall : ∀ k, s k = true := by
      intro k; induction k with
      | zero => rw [← h, zfcF_fin hs]
      | succ k ih => rw [← h, zfcF_fin hs]; exact ih
    refine (infinite_of_forall_exists_gt fun n => ⟨n + 1, ?_, by omega⟩ : Set.Infinite _) hs
    exact hall _
  · obtain ⟨k, -, hk⟩ := exists_true_ge hs 0
    rw [← h, zfcF_inf hs] at hk; exact Bool.false_ne_true hk

theorem zfcF_exclusive : Exclusive zfcF := by
  classical
  intro s s' hne
  by_cases hs : FinSupp s <;> by_cases hs' : FinSupp s'
  · have hex : ∃ k, s k ≠ s' k := Function.ne_iff.1 hne
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rw [zfcF_fin hs, zfcF_fin hs']
    rcases hm : Nat.find hex with _ | m
    · rfl
    · have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
  · obtain ⟨k, hk, he⟩ := cross hs' hs; exact ⟨k, Ne.symm hk, he.symm⟩
  · exact cross hs hs'
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    exact ⟨k, hk, by rw [zfcF_inf hs, zfcF_inf hs']⟩

/-- **Main theorem (ZFC).** An exclusive, fixed-point-free self-map of `ℕ → Bool`. -/
theorem exists_exclusive_fixedPointFree :
    ∃ F : (ℕ → Bool) → (ℕ → Bool), (∀ s, F s ≠ s) ∧ Exclusive F :=
  ⟨zfcF, zfcF_ne, zfcF_exclusive⟩

/-- **Corollary (ZFC).** An exclusive process on countably many binary parties that is not a
process function. -/
theorem exists_exclusive_not_pf :
    ∃ (I : ℕ → Type) (w : (ℕ → Bool) → (∀ k, I k)), Exclusive w ∧ ¬ IsProcessFunction w :=
  (exists_exclusive_not_pf_iff (fun _ : ℕ => Bool)).2 exists_exclusive_fixedPointFree

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_exclusive_fixedPointFree
#print axioms PFUL.Infinite.exists_exclusive_not_pf
