/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Linking the H.12 counterexample to the general process-function framework

`PFUL.Counterexample` uses its own finite encodings: strings are `Fin 8`, a process function is
`IsPF w` (unique fixed point of `o ↦ applyF F (w o)`), and validity is `Valid` (total probability
1 under product stochastic interventions). Here we show:

* `isPF_iff` : `IsPF w` is exactly `PFUL.Countable.IsProcessFunction` (the arbitrary-alphabet
  definition used in `Countable`, `Rows`, `Assemble`, `KrausL2`) for the bit-string form `wBits w`;
* `isPF_iff_column` : the same for `PFUL.Column.IsProcessFunction` (finite alphabets);
* `valid_pfPoint` : every process function's 0/1 process is `Valid`, via the general column
  identity `PFUL.Column.sum_prod_eq_one` (logical consistency under stochastic interventions);
* `valid_of_mem_convexHull` : so is everything in `convexHull ℝ PFset`;
* `purification_conjecture_false'` : the H.12 theorem restated with the general definition.
-/
import PFUL.Counterexample
import PFUL.Column
import PFUL.Countable

open Finset

namespace PFUL.Counterexample

/-- `Fin 8` as 3-bit strings, party `k` reading `bit k`. -/
def bitsEquiv : Fin 8 ≃ (Fin 3 → Bool) where
  toFun x k := bit k x
  invFun b := ofBits (b 0) (b 1) (b 2)
  left_inv := by decide
  right_inv := by intro b; funext k; revert b k; decide

theorem bit_ext {x y : Fin 8} (h : ∀ k, bit k x = bit k y) : x = y :=
  bitsEquiv.injective (funext h)

theorem bit_applyF (F : Fin 3 → Bool × Bool) (i : Fin 8) (k : Fin 3) :
    bit k (applyF F i) = loc (F k) (bit k i) := by
  revert F i k; decide

/-- The bit-string form of a map `w : Fin 8 → Fin 8`. -/
def wBits (w : Fin 8 → Fin 8) : (Fin 3 → Bool) → (Fin 3 → Bool) :=
  fun s k => bit k (w (bitsEquiv.symm s))

theorem loc_pair (f : Bool → Bool) : loc (f false, f true) = f := by
  funext x; cases x <;> rfl

theorem fixed_iff (w : Fin 8 → Fin 8) (F : Fin 3 → Bool × Bool) (o : Fin 8) :
    applyF F (w o) = o ↔ ∀ k, loc (F k) (wBits w (bitsEquiv o) k) = bitsEquiv o k := by
  have hs : bitsEquiv.symm (bitsEquiv o) = o := bitsEquiv.symm_apply_apply o
  simp only [wBits, hs]
  constructor
  · intro h k; rw [← bit_applyF, h]; rfl
  · intro h; exact bit_ext fun k => by rw [bit_applyF]; exact h k

/-- `IsPF` is the general (arbitrary-alphabet) process-function property. -/
theorem isPF_iff (w : Fin 8 → Fin 8) :
    IsPF w ↔ PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) := by
  constructor
  · intro hw f
    obtain ⟨o, ho, hu⟩ := hw (fun k => (f k false, f k true))
    refine ⟨bitsEquiv o, ?_, fun s hs => ?_⟩
    · have := (fixed_iff w _ o).1 ho; simpa [loc_pair] using this
    · have h1 : applyF (fun k => (f k false, f k true)) (w (bitsEquiv.symm s)) =
          bitsEquiv.symm s := by
        rw [fixed_iff]; simpa [loc_pair] using hs
      rw [← hu _ h1]; exact (bitsEquiv.apply_symm_apply s).symm
  · intro hw F
    obtain ⟨s, hs, hu⟩ := hw (fun k => loc (F k))
    refine ⟨bitsEquiv.symm s, ?_, fun o ho => ?_⟩
    · show applyF F (w (bitsEquiv.symm s)) = bitsEquiv.symm s
      rw [fixed_iff]; simpa using hs
    · have := hu (bitsEquiv o) ((fixed_iff w F o).1 ho)
      rw [← this]; exact (bitsEquiv.symm_apply_apply o).symm

theorem isPF_iff_column (w : Fin 8 → Fin 8) :
    IsPF w ↔ PFUL.Column.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) := by
  rw [isPF_iff]; rfl

/-- Every process function's deterministic process is valid under all local stochastic
interventions (general column identity, `PFUL.Column.sum_prod_eq_one`). -/
theorem valid_pfPoint {w : Fin 8 → Fin 8} (hw : IsPF w) : Valid (pfPoint w) := by
  refine ⟨fun i o => by unfold pfPoint; split_ifs <;> norm_num, fun q _ hq => ?_⟩
  have key := PFUL.Column.sum_prod_eq_one (R := ℝ) (wBits w) ((isPF_iff_column w).1 hw)
    (fun k x y => q k x y) (fun k x => by simpa [Fintype.sum_bool, add_comm] using hq k x)
  rw [← key, ← bitsEquiv.sum_comp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single (w o)]
  · have hs : bitsEquiv.symm (bitsEquiv o) = o := bitsEquiv.symm_apply_apply o
    simp only [pfPoint, wBits, hs, ↓reduceIte, one_mul]; rfl
  · intro i _ hi; simp [pfPoint, Ne.symm hi]
  · simp

theorem valid_of_mem_convexHull {p : Fin 8 → Fin 8 → ℝ} (hp : p ∈ convexHull ℝ PFset) :
    Valid p := by
  have hconv : Convex ℝ {p | Valid p} := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i o => ?_, fun q hq0 hq => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx.1 i o)) (mul_nonneg hb (hy.1 i o))
    · have h1 := hx.2 q hq0 hq; have h2 := hy.2 q hq0 hq
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum, h1, h2, mul_one, hab]
  refine convexHull_min ?_ hconv hp
  rintro _ ⟨w, hw, rfl⟩; exact valid_pfPoint hw

/-- H.12 with the general process-function definition. -/
theorem purification_conjecture_false' :
    ∃ p : Fin 8 → Fin 8 → ℝ, Valid p ∧ Purifiable p ∧
      p ∉ convexHull ℝ {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
        (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} := by
  obtain ⟨p, h1, h2, h3⟩ := purification_conjecture_false
  refine ⟨p, h1, h2, ?_⟩
  have : {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} = PFset := by
    ext x; simp only [PFset, Set.mem_ofPred_eq, isPF_iff]
  rwa [this]

end PFUL.Counterexample
