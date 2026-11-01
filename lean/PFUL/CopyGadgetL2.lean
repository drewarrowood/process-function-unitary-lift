/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Theorem 1.2 (⇒) on countable alphabets: the copy gadget on ℓ² (Claim C.1)

Alphabets are countable (finite or infinite), output alphabets carry an additive group
structure. If `w` is not a process function, the copy-gadget kernels
`V k (o, y) (i, x) = [o = f k i + x ∧ y = i]` satisfy the hypotheses of
`PFUL.Countable.induced_unitary_l2` (square-summable rows, orthonormal rows, unit columns),
yet no linear isometry `ℓ²(sources) → ℓ²(sinks)` has the induced kernel as its matrix:
column `(0,0)` has squared norm `N(f) ≠ 1` (when `N(f) = ∞` the column is not even in ℓ²).
Combined with `induced_unitary_l2` this gives the iff `unitary_l2_iff_pf`.
-/
import PFUL.Assemble

open scoped InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false

namespace PFUL.Countable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, AddCommGroup (O k)]
variable [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

/-- Copy-gadget kernel `(i, x) ↦ (f i + x, i)` for party `k`. -/
def gadgetK (f : ∀ k, I k → O k) (k : ι) : O k × I k → I k × O k → ℂ :=
  fun r c => if r = (f k c.1 + c.2, c.1) then 1 else 0

lemma gadgetK_eq_iff (f : ∀ k, I k → O k) (k : ι) (r : O k × I k) (c : I k × O k) :
    r = (f k c.1 + c.2, c.1) ↔ c = (r.2, r.1 - f k r.2) := by
  obtain ⟨o, y⟩ := r; obtain ⟨i, x⟩ := c
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨rfl, by rw [h1]; abel⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨by abel, rfl⟩

lemma gadgetK_row (f : ∀ k, I k → O k) (k : ι) (r : O k × I k) :
    gadgetK f k r = fun c => if c = (r.2, r.1 - f k r.2) then 1 else 0 := by
  funext c; simp only [gadgetK, gadgetK_eq_iff]

lemma gadgetK_sq (f : ∀ k, I k → O k) (k : ι) (a : O k × I k) :
    Summable fun c => ‖gadgetK f k a c‖ ^ 2 := by
  rw [gadgetK_row]
  refine (hasSum_ite_eq (a.2, a.1 - f k a.2) (1 : ℝ)).summable.congr fun c => ?_
  split_ifs with h <;> simp [h]

lemma gadgetK_rows (f : ∀ k, I k → O k) (k : ι) (a b : O k × I k) :
    HasSum (fun c => gadgetK f k a c * star (gadgetK f k b c)) (if a = b then 1 else 0) := by
  rw [gadgetK_row, gadgetK_row]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    convert hasSum_ite_eq (a.2, a.1 - f k a.2) (1 : ℂ) using 1
    funext c; split_ifs <;> simp
  · simp only [hab, if_false]
    convert hasSum_zero (α := ℂ) (β := I k × O k) using 1
    funext c
    by_cases h1 : c = (a.2, a.1 - f k a.2)
    · have h2 : c ≠ (b.2, b.1 - f k b.2) := by
        rintro rfl
        apply hab
        obtain ⟨o, y⟩ := a; obtain ⟨o', y'⟩ := b
        simp only [Prod.mk.injEq] at h1
        obtain ⟨rfl, h⟩ := h1
        simp only [sub_left_inj] at h
        rw [h]
      rw [if_pos h1, if_neg h2]; simp
    · simp [h1]

lemma gadgetK_col (f : ∀ k, I k → O k) (k : ι) (c : I k × O k) :
    ∑' r, ((‖gadgetK f k r c‖₊ : ENNReal)) ^ 2 = 1 := by
  have : (fun r => ((‖gadgetK f k r c‖₊ : ENNReal)) ^ 2)
      = fun r => if r = (f k c.1 + c.2, c.1) then 1 else 0 := by
    funext r; simp only [gadgetK]; split_ifs <;> simp
  rw [this, tsum_ite_eq]

/-- Column `(0,0)` of the induced copy-gadget kernel. -/
lemma induced_gadget_col0 (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, I k → O k)
    (r : (∀ k, O k) × (∀ k, I k)) :
    (∏ k, gadgetK f k (r.1 k, r.2 k) (w r.1 k + (0 : ∀ k, I k) k, (0 : ∀ k, O k) k))
      = if (∀ k, f k (w r.1 k) = r.1 k) ∧ r.2 = w r.1 then 1 else 0 := by
  obtain ⟨s, y⟩ := r
  simp only [gadgetK, Pi.zero_apply, add_zero, Prod.mk.injEq]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h; exact ⟨fun k => (h k).1.symm, funext fun k => (h k).2⟩
  · rintro ⟨h1, h2⟩ k; exact ⟨(h1 k).symm, congrFun h2 k⟩

variable [∀ k, Countable (I k)] [∀ k, Countable (O k)]

/-- **Claim C.1 (Lean).** If the closed copy-gadget loop is realised by a linear isometry of ℓ²
(matrix entries `Φ (single c 1) r = M r c`), then `f ∘ w` has exactly one fixed point. -/
theorem existsUnique_of_isometry_l2 (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, I k → O k)
    (Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2)
    (hΦ : ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
      = ∏ k, gadgetK f k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  set v := Φ (lp.single 2 (0 : (∀ k, I k) × (∀ k, O k)) (1 : ℂ))
  set P : (∀ k, O k) × (∀ k, I k) → Prop := fun r => (∀ k, f k (w r.1 k) = r.1 k) ∧ r.2 = w r.1
  have hv : ∀ r, ‖v r‖ ^ 2 = if P r then 1 else 0 := by
    intro r
    simp only [v, hΦ, Prod.fst_zero, Prod.snd_zero, induced_gadget_col0, P]
    split_ifs <;> simp
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hnorm : ‖v‖ = 1 := by
    simp only [v, Φ.norm_map, lp.norm_single (p := 2) (by norm_num)]; simp
  have hsum := lp.norm_rpow_eq_tsum hp v
  have hsumm : Summable fun r => ‖v r‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp v).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hnorm, one_pow] at hsum hsumm
  simp_rw [hv] at hsum hsumm
  -- existence
  have hex : ∃ r, P r := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨r0, hr0⟩ := hex
  refine ⟨r0.1, hr0.1, fun s hs => ?_⟩
  by_contra hne
  let a : (∀ k, O k) × (∀ k, I k) := (s, w s)
  have hPa : P a := ⟨hs, rfl⟩
  have hab : a ≠ r0 := fun h => hne (by rw [← h])
  have hle := hsumm.sum_le_tsum ({a, r0} : Finset _) (fun r _ => by split_ifs <;> norm_num)
  rw [Finset.sum_pair hab, if_pos hPa, if_pos hr0, ← hsum] at hle
  norm_num at hle

/-- **Theorem 1.2 (⇒), countable alphabets, no isometric realisation.** If `w` is not a process
function, the copy gadget satisfies every hypothesis of `induced_unitary_l2`, but no linear
isometry of ℓ² has the induced kernel as matrix. -/
theorem not_isometry_of_not_pf_l2 (w : (∀ k, O k) → (∀ k, I k)) (hw : ¬ IsProcessFunction w) :
    ∃ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) ∧
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) ∧
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) ∧
      ¬ ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) := by
  unfold IsProcessFunction at hw
  push Not at hw
  obtain ⟨f, hf⟩ := hw
  refine ⟨gadgetK f, gadgetK_sq f, gadgetK_rows f, gadgetK_col f, ?_⟩
  rintro ⟨Φ, hΦ⟩
  obtain ⟨s, hs, hu⟩ := existsUnique_of_isometry_l2 w f Φ hΦ
  exact hf ⟨s, hs, hu⟩

/-- **Theorem 1.2 on countable alphabets (both directions, ancillas `X k = O k`, `Y k = I k`).**
The closed loop is realised by a unitary of ℓ² for every admissible tuple of local kernels iff
`w` is a process function. -/
theorem unitary_l2_iff_pf (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))
    ↔ IsProcessFunction w := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨V, h1, h2, h3, hno⟩ := not_isometry_of_not_pf_l2 w hw
    obtain ⟨Φ, hΦ⟩ := h V h1 h2 h3
    exact hno ⟨Φ.toLinearIsometry, hΦ⟩
  · intro hw V h1 h2 h3
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2 w hw V h1 h2 h3
    exact ⟨Φ, hΦ⟩

end PFUL.Countable
