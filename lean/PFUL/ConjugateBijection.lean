/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# The conjugate reframing of exclusivity (binary parties)

For `F : (ι → Bool) → (ι → Bool)` let `conj F s = F s xor s` (Richard's conjugate,
arXiv:1302.6346; the finite criterion "each subnetwork has a unique fixed point iff the conjugate
of each subnetwork is a bijection" is Richard/Ruet). We prove, for an arbitrary index type `ι`:

* `exclusive_iff_conj_injOn`: `Exclusive F` iff for every subcube
  `cube D z = {s | ∀ k ∉ D, s k = z k}` the restricted conjugate `s ↦ (conj F s)|_D` is injective
  on `cube D z`.
* finite `ι`: exclusive ⇒ a fixed point exists (injective ⇒ bijective), hence exclusive ⇒ PF.
* the ZFC counterexample `zfcF` has an injective conjugate that misses `0`.
-/
import PFUL.ZFCCounterexample

open Set

namespace PFUL.Infinite

variable {ι : Type*}

/-- Richard's conjugate. -/
def conj (F : (ι → Bool) → (ι → Bool)) (s : ι → Bool) : ι → Bool := fun k => xor (F s k) (s k)

/-- The subcube with free coordinates `D` through `z`. -/
def cube (D : Set ι) (z : ι → Bool) : Set (ι → Bool) := {s | ∀ k, k ∉ D → s k = z k}

lemma xor_eq_iff_of_ne {a b c d : Bool} (h : c ≠ d) : a = b ↔ xor a c ≠ xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Pointwise form: exclusivity ⇔ for `s ≠ s'` the conjugates differ somewhere `s, s'` differ. -/
theorem exclusive_iff_conj (F : (ι → Bool) → (ι → Bool)) :
    Exclusive F ↔ ∀ s s', s ≠ s' → ∃ k, s k ≠ s' k ∧ conj F s k ≠ conj F s' k := by
  unfold Exclusive
  refine forall_congr' fun s => forall_congr' fun s' => forall_congr' fun _ => ?_
  exact exists_congr fun k => and_congr_right fun h => xor_eq_iff_of_ne h

/-- **Subcube form.** Exclusivity ⇔ the conjugate, read on the free coordinates, is injective on
every subcube. -/
theorem exclusive_iff_conj_injOn (F : (ι → Bool) → (ι → Bool)) :
    Exclusive F ↔ ∀ (D : Set ι) (z : ι → Bool),
      InjOn (fun s => fun k : D => conj F s k) (cube D z) := by
  rw [exclusive_iff_conj]
  constructor
  · intro h D z s hs s' hs' heq
    by_contra hne
    obtain ⟨k, hk, hc⟩ := h s s' hne
    have hkD : k ∈ D := by
      by_contra hkD; exact hk ((hs k hkD).trans (hs' k hkD).symm)
    exact hc (congrFun heq ⟨k, hkD⟩)
  · intro h s s' hne
    by_contra hall
    push Not at hall
    refine hne (h {k | s k ≠ s' k} s (fun k hk => rfl) (fun k hk => ?_) ?_)
    · simpa [eq_comm] using hk
    · funext ⟨k, hk⟩; exact hall k hk

/-- On the full cube (`D = univ`) the conjugate of an exclusive map is injective. -/
theorem conj_injective_of_exclusive {F : (ι → Bool) → (ι → Bool)} (h : Exclusive F) :
    Function.Injective (conj F) := by
  intro s s' heq
  by_contra hne
  obtain ⟨k, -, hc⟩ := (exclusive_iff_conj F).1 h s s' hne
  exact hc (congrFun heq k)

lemma conj_eq_zero_iff (F : (ι → Bool) → (ι → Bool)) (s : ι → Bool) :
    conj F s = (fun _ => false) ↔ F s = s := by
  simp only [funext_iff, conj]
  exact forall_congr' fun k => by cases F s k <;> cases s k <;> simp

/-- **Finite parties:** exclusive ⇒ a fixed point exists (injective ⇒ surjective). -/
theorem exists_fixed_of_exclusive [Finite ι] {F : (ι → Bool) → (ι → Bool)} (h : Exclusive F) :
    ∃ s, F s = s := by
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.1 (conj_injective_of_exclusive h))
    (fun _ => false)
  exact ⟨s, (conj_eq_zero_iff F s).1 hs⟩

/-- **Finite binary parties: exclusive ⇒ process function**, via the conjugate. -/
theorem isProcessFunction_of_exclusive [Finite ι] {I : ι → Type*}
    {w : (ι → Bool) → (∀ k, I k)} (h : Exclusive w) : IsProcessFunction w := by
  intro f
  have hF : Exclusive (fun s k => f k (w s k)) := by
    intro s s' hne
    obtain ⟨k, hk, hw⟩ := h s s' hne
    exact ⟨k, hk, by simp only [hw]⟩
  obtain ⟨s, hs⟩ := exists_fixed_of_exclusive hF
  have hs' : ∀ k, f k (w s k) = s k := fun k => congrFun hs k
  exact ⟨s, hs', fun t ht => fixed_unique h f ht hs'⟩

/-- **The ZFC counterexample in conjugate form:** injective conjugate that misses `0`. -/
theorem zfcF_conj_injective_not_surjective :
    Function.Injective (conj zfcF) ∧ ∀ s, conj zfcF s ≠ fun _ => false :=
  ⟨conj_injective_of_exclusive zfcF_exclusive,
    fun s h => zfcF_ne s ((conj_eq_zero_iff zfcF s).1 h)⟩

end PFUL.Infinite

#print axioms PFUL.Infinite.exclusive_iff_conj_injOn
#print axioms PFUL.Infinite.isProcessFunction_of_exclusive
#print axioms PFUL.Infinite.zfcF_conj_injective_not_surjective
