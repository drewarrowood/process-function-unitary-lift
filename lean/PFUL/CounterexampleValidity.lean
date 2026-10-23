/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 10: the counterexample's `Valid` and `PFUL.ValidWith`

`PFUL.ValidWith w X Y` is the quantum (AFNB) validity of the source-sink lift of a
*deterministic* map `w`. For deterministic classical processes `pfPoint w` we prove

  `Valid (pfPoint w) ↔ IsPF w`, and then `Valid (pfPoint w) → ValidWith (wBits w) X Y`
  for all finite ancilla families `X`, `Y`.

`ValidWith` is stated over alphabets with an additive group structure (a section variable of
`PFUL.Validity`); on `Bool` we use the `ZMod 2 = Fin 2` structure transported along
`finTwoEquiv` (the result does not depend on it).
-/
import PFUL.CounterexampleLink
import PFUL.Validity

open Finset

namespace PFUL.Counterexample

/-- Bitwise deterministic interventions are valid-test witnesses: a valid deterministic process
has exactly one fixed point for every local deterministic intervention. -/
theorem isPF_of_valid_pfPoint {w : Fin 8 → Fin 8} (h : Valid (pfPoint w)) : IsPF w := by
  intro F
  set q : Fin 3 → Bool → Bool → ℝ := fun k x y => if loc (F k) x = y then 1 else 0 with hq
  have hq0 : ∀ k x y, 0 ≤ q k x y := fun k x y => by simp only [hq]; split_ifs <;> norm_num
  have hq1 : ∀ k x, q k x false + q k x true = 1 := by
    intro k x; simp only [hq]; cases loc (F k) x <;> simp
  have hprod : ∀ i o : Fin 8, ∏ k, q k (bit k i) (bit k o) = if applyF F i = o then 1 else 0 := by
    intro i o
    by_cases hio : applyF F i = o
    · subst hio
      simp only [hq, ← bit_applyF, ↓reduceIte, Finset.prod_const_one]
    · simp only [hio, ↓reduceIte]
      have : ∃ k, loc (F k) (bit k i) ≠ bit k o := by
        by_contra hc; push Not at hc
        exact hio (bit_ext fun k => by rw [bit_applyF]; exact hc k)
      obtain ⟨k, hk⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hq, hk])
  have hsum := h.2 q hq0 hq1
  simp_rw [hprod] at hsum
  rw [Finset.sum_comm] at hsum
  have hs : ∀ o : Fin 8, ∑ i : Fin 8, pfPoint w i o * (if applyF F i = o then 1 else 0) =
      if applyF F (w o) = o then 1 else 0 := by
    intro o
    rw [Finset.sum_eq_single (w o)]
    · simp [pfPoint]
    · intro i _ hi; simp [pfPoint, Ne.symm hi]
    · simp
  simp_rw [hs] at hsum
  rw [Finset.sum_boole] at hsum
  have hcard : (Finset.univ.filter fun o => applyF F (w o) = o).card = 1 := by exact_mod_cast hsum
  obtain ⟨o, ho⟩ := Finset.card_eq_one.1 hcard
  refine ⟨o, ?_, fun o' ho' => ?_⟩
  · have : o ∈ Finset.univ.filter fun o => applyF F (w o) = o := by rw [ho]; simp
    simpa using this
  · have : o' ∈ Finset.univ.filter fun o => applyF F (w o) = o := by simpa using ho'
    rw [ho] at this; simpa using this

/-- For deterministic processes, the counterexample's classical validity is exactly the
process-function property. -/
theorem valid_pfPoint_iff (w : Fin 8 → Fin 8) : Valid (pfPoint w) ↔ IsPF w :=
  ⟨isPF_of_valid_pfPoint, valid_pfPoint⟩

/-- The `ZMod 2` group structure on `Bool`, used only to state `ValidWith`. -/
@[reducible] def boolAddCommGroup : AddCommGroup Bool := finTwoEquiv.symm.addCommGroup

attribute [local instance] boolAddCommGroup

/-- **Validity link.** A deterministic classical process that is `Valid` (classical, all local
stochastic interventions) has an AFNB-valid source-sink lift, `PFUL.ValidWith`, for all finite
ancillas. -/
theorem validWith_of_valid_pfPoint {w : Fin 8 → Fin 8} (h : Valid (pfPoint w))
    (X Y : Fin 3 → Type) [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
    [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)] :
    PFUL.ValidWith (I := fun _ : Fin 3 => Bool) (O := fun _ : Fin 3 => Bool) (wBits w) X Y :=
  PFUL.valid _ ((isPF_iff_column w).1 (isPF_of_valid_pfPoint h)) X Y

end PFUL.Counterexample
