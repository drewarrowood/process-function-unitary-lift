/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 10: row orthonormality of the Switchboard composition

The dual of `scalar_key`: summing over the *columns* of the composed map. Finite part: 64 slot
combinations, checked exactly over the Gaussian integers by kernel computation.
-/
import PFUL.CounterexampleInf

open Complex Finset

namespace PFUL.Counterexample

/-- Row slot matrices: `0 ↦ E₁₁`, `1 ↦ E₀₀ - E₁₁`, `2 ↦ E₀₁`, `3 ↦ E₁₀`. -/
def rowW (j : Fin 4) (y z : Bool) : ℤ :=
  if j = 0 then (if y = true ∧ z = true then 1 else 0)
  else if j = 1 then (if y = z then (if y then -1 else 1) else 0)
  else if j = 2 then (if y = false ∧ z = true then 1 else 0)
  else (if y = true ∧ z = false then 1 else 0)

/-- Flip forced by a row slot. -/
def rdj (j : Fin 4) : Bool := decide (2 ≤ j.val)

theorem rowW_ne : ∀ (j : Fin 4) (y z : Bool), rowW j y z ≠ 0 → xor y z = rdj j := by decide

def RW (J : Fin 3 → Fin 4) (e e' : Fin 8) : ℤ :=
  rowW (J 0) (bit 0 e) (bit 0 e') * rowW (J 1) (bit 1 e) (bit 1 e') *
    rowW (J 2) (bit 2 e) (bit 2 e')

def rδJ (J : Fin 3 → Fin 4) : Fin 8 := ofBits (rdj (J 0)) (rdj (J 1)) (rdj (J 2))

/-- `64 R(J)[o,o';δ]`. -/
def RD (J : Fin 3 → Fin 4) (o o' δ : Fin 8) : GI :=
  ∑ e : Fin 8, ∑ s : Fin 8, (if RW J e (e ^^^ δ) = 0 then 0 else
    RW J e (e ^^^ δ) • gmul (tab o e s) (gconj (tab o' (e ^^^ δ) s)))

/-- Slot `0` (trace part) is only allowed where the two row bits agree. -/
def rowAllowed (J : Fin 3 → Fin 4) (o o' : Fin 8) : Bool :=
  (!(J 0 == 0) || bit 0 o == bit 0 o') && (!(J 1 == 0) || bit 1 o == bit 1 o') &&
    (!(J 2 == 0) || bit 2 o == bit 2 o')

def rowBlock (j0 j1 : Fin 4) : Bool :=
  (List.finRange 4).all fun j2 => (List.finRange 8).all fun o => (List.finRange 8).all fun o' =>
    !(rowAllowed ![j0, j1, j2] o o') ||
      RD ![j0, j1, j2] o o' (rδJ ![j0, j1, j2]) ==
        (if j0 = 0 ∧ j1 = 0 ∧ j2 = 0 ∧ o = o' then ((64 : ℤ), (0 : ℤ)) else 0)

theorem rowBlock_0_0 : rowBlock 0 0 = true := by decide +kernel
theorem rowBlock_0_1 : rowBlock 0 1 = true := by decide +kernel
theorem rowBlock_0_2 : rowBlock 0 2 = true := by decide +kernel
theorem rowBlock_0_3 : rowBlock 0 3 = true := by decide +kernel
theorem rowBlock_1_0 : rowBlock 1 0 = true := by decide +kernel
theorem rowBlock_1_1 : rowBlock 1 1 = true := by decide +kernel
theorem rowBlock_1_2 : rowBlock 1 2 = true := by decide +kernel
theorem rowBlock_1_3 : rowBlock 1 3 = true := by decide +kernel
theorem rowBlock_2_0 : rowBlock 2 0 = true := by decide +kernel
theorem rowBlock_2_1 : rowBlock 2 1 = true := by decide +kernel
theorem rowBlock_2_2 : rowBlock 2 2 = true := by decide +kernel
theorem rowBlock_2_3 : rowBlock 2 3 = true := by decide +kernel
theorem rowBlock_3_0 : rowBlock 3 0 = true := by decide +kernel
theorem rowBlock_3_1 : rowBlock 3 1 = true := by decide +kernel
theorem rowBlock_3_2 : rowBlock 3 2 = true := by decide +kernel
theorem rowBlock_3_3 : rowBlock 3 3 = true := by decide +kernel

theorem rowBlock_all : ∀ j0 j1 : Fin 4, rowBlock j0 j1 = true
  | ⟨0, _⟩, ⟨0, _⟩ => rowBlock_0_0
  | ⟨0, _⟩, ⟨1, _⟩ => rowBlock_0_1
  | ⟨0, _⟩, ⟨2, _⟩ => rowBlock_0_2
  | ⟨0, _⟩, ⟨3, _⟩ => rowBlock_0_3
  | ⟨1, _⟩, ⟨0, _⟩ => rowBlock_1_0
  | ⟨1, _⟩, ⟨1, _⟩ => rowBlock_1_1
  | ⟨1, _⟩, ⟨2, _⟩ => rowBlock_1_2
  | ⟨1, _⟩, ⟨3, _⟩ => rowBlock_1_3
  | ⟨2, _⟩, ⟨0, _⟩ => rowBlock_2_0
  | ⟨2, _⟩, ⟨1, _⟩ => rowBlock_2_1
  | ⟨2, _⟩, ⟨2, _⟩ => rowBlock_2_2
  | ⟨2, _⟩, ⟨3, _⟩ => rowBlock_2_3
  | ⟨3, _⟩, ⟨0, _⟩ => rowBlock_3_0
  | ⟨3, _⟩, ⟨1, _⟩ => rowBlock_3_1
  | ⟨3, _⟩, ⟨2, _⟩ => rowBlock_3_2
  | ⟨3, _⟩, ⟨3, _⟩ => rowBlock_3_3
  | ⟨n + 4, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 4, h⟩ => absurd h (by omega)

theorem RW_ne {J : Fin 3 → Fin 4} {e δ : Fin 8} (h : RW J e (e ^^^ δ) ≠ 0) : δ = rδJ J := by
  simp only [RW, ne_eq, mul_eq_zero, not_or] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have k0 := rowW_ne _ _ _ h0
  have k1 := rowW_ne _ _ _ h1
  have k2 := rowW_ne _ _ _ h2
  rw [bit_xor] at k0 k1 k2
  rw [rδJ, eq_ofBits_iff]
  refine ⟨?_, ?_, ?_⟩ <;> [rw [← k0]; rw [← k1]; rw [← k2]] <;>
    cases bit _ e <;> cases bit _ δ <;> rfl

theorem fin3_eta4 (J : Fin 3 → Fin 4) : ![J 0, J 1, J 2] = J := by
  funext k; fin_cases k <;> rfl

theorem RD_eq (J : Fin 3 → Fin 4) (o o' δ : Fin 8) (hA : rowAllowed J o o' = true) :
    RD J o o' δ = if J = 0 ∧ o = o' ∧ δ = 0 then ((64 : ℤ), (0 : ℤ)) else 0 := by
  by_cases hδ : δ = rδJ J
  · subst hδ
    have := all_finRange (all_finRange (all_finRange (rowBlock_all (J 0) (J 1)) (J 2)) o) o'
    rw [fin3_eta4, hA] at this
    have hJ : J = 0 ↔ J 0 = 0 ∧ J 1 = 0 ∧ J 2 = 0 := by
      constructor
      · rintro rfl; simp
      · rintro ⟨a, b, c⟩; funext k; fin_cases k <;> assumption
    have h0 : J = 0 → rδJ J = 0 := by rintro rfl; rfl
    simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at this
    rw [this]
    have hiff : (J 0 = 0 ∧ J 1 = 0 ∧ J 2 = 0 ∧ o = o') ↔ (J = 0 ∧ o = o' ∧ rδJ J = 0) := by
      constructor
      · rintro ⟨a, b, c, d⟩
        have hJ0 := hJ.2 ⟨a, b, c⟩
        exact ⟨hJ0, d, h0 hJ0⟩
      · rintro ⟨a, d, -⟩
        exact ⟨(hJ.1 a).1, (hJ.1 a).2.1, (hJ.1 a).2.2, d⟩
    exact if_congr hiff rfl rfl
  · have hz : RD J o o' δ = 0 := by
      apply Finset.sum_eq_zero; intro e _
      apply Finset.sum_eq_zero; intro s _
      have : RW J e (e ^^^ δ) = 0 := by
        by_contra h; exact hδ (RW_ne h)
      simp [this]
    rw [hz]
    have : ¬ (J = 0 ∧ o = o' ∧ δ = 0) := by
      rintro ⟨rfl, -, rfl⟩; exact hδ rfl
    simp [this]

theorem rowTC_eq (J : Fin 3 → Fin 4) (o o' δ : Fin 8) (hA : rowAllowed J o o' = true) :
    ∑ e : Fin 8, ∑ s : Fin 8, board o e s * star (board o' (e ^^^ δ) s) *
        ∏ k, (rowW (J k) (bit k e) (bit k (e ^^^ δ)) : ℂ) =
      if J = 0 ∧ o = o' ∧ δ = 0 then 1 else 0 := by
  have h := congrArg toC (RD_eq J o o' δ hA)
  rw [RD, toC_sum] at h
  simp only [toC_sum] at h
  have key : ∀ e s, toC (if RW J e (e ^^^ δ) = 0 then 0 else
      RW J e (e ^^^ δ) • gmul (tab o e s) (gconj (tab o' (e ^^^ δ) s))) =
      64 * (board o e s * star (board o' (e ^^^ δ) s) *
        ∏ k, (rowW (J k) (bit k e) (bit k (e ^^^ δ)) : ℂ)) := by
    intro e s
    have hw : (if RW J e (e ^^^ δ) = 0 then (0 : GI) else
        RW J e (e ^^^ δ) • gmul (tab o e s) (gconj (tab o' (e ^^^ δ) s))) =
        RW J e (e ^^^ δ) • gmul (tab o e s) (gconj (tab o' (e ^^^ δ) s)) := by
      split_ifs with h0 <;> simp [h0]
    rw [hw, toC_smul, toC_mul, toC_gconj, board_apply, board_apply, Fin.prod_univ_three, RW]
    rw [star_div₀]; simp only [star_ofNat]; push_cast; ring
  simp only [key, ← Finset.mul_sum] at h
  have h64 : (64 : ℂ) ≠ 0 := by norm_num
  split_ifs at h ⊢ with hc
  · rw [show toC ((64 : ℤ), (0 : ℤ)) = 64 by simp [toC]] at h
    exact (mul_eq_left₀ h64).1 h
  · rw [toC_zero] at h
    exact (mul_eq_zero.1 h).resolve_left h64

/-- Coefficients of a `2 × 2` matrix in the row slot basis (slot `0` carries the trace). -/
def rcoef (R : Bool → Bool → ℂ) (j : Fin 4) : ℂ :=
  if j = 0 then R false false + R true true else if j = 1 then R false false
  else if j = 2 then R false true else R true false

theorem rdecomp (R : Bool → Bool → ℂ) (y z : Bool) :
    R y z = ∑ j : Fin 4, rcoef R j * (rowW j y z : ℂ) := by
  rw [Fin.sum_univ_four]
  cases y <;> cases z <;> simp [rcoef, rowW]

/-- **Row scalar key.** The dual of `scalar_key`: with `tr R_k = [o_k = o'_k] c_k`,
`Σ_e Σ_s U_o[e,s] conj U_{o'}[e⊕δ,s] Π_k R_k[e_k, (e⊕δ)_k] = [o = o' ∧ δ = 0] Π_k c_k`. -/
theorem row_scalar_key (R : Fin 3 → Bool → Bool → ℂ) (c : Fin 3 → ℂ) (o o' δ : Fin 8)
    (hR : ∀ k, R k false false + R k true true = if bit k o = bit k o' then c k else 0) :
    ∑ e : Fin 8, ∑ s : Fin 8, board o e s * star (board o' (e ^^^ δ) s) *
        ∏ k, R k (bit k e) (bit k (e ^^^ δ)) =
      if o = o' ∧ δ = 0 then ∏ k, c k else 0 := by
  have hexp : ∀ e, ∏ k, R k (bit k e) (bit k (e ^^^ δ)) =
      ∑ J : Fin 3 → Fin 4, (∏ k, rcoef (R k) (J k)) *
        ∏ k, (rowW (J k) (bit k e) (bit k (e ^^^ δ)) : ℂ) := by
    intro e
    simp_rw [fun k => rdecomp (R k)]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]
  have hterm : ∀ J : Fin 3 → Fin 4, ∑ e : Fin 8, ∑ s : Fin 8,
      board o e s * star (board o' (e ^^^ δ) s) * ((∏ k, rcoef (R k) (J k)) *
        ∏ k, (rowW (J k) (bit k e) (bit k (e ^^^ δ)) : ℂ)) =
      (∏ k, rcoef (R k) (J k)) * (if J = 0 ∧ o = o' ∧ δ = 0 then 1 else 0) := by
    intro J
    by_cases hA : rowAllowed J o o' = true
    · rw [← rowTC_eq J o o' δ hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    · have hz : ∏ k, rcoef (R k) (J k) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        simp only [rowAllowed, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          beq_eq_false_iff_ne, beq_iff_eq, not_and_or, not_or] at hA
        have hk : ∀ k, J k = 0 → bit k o ≠ bit k o' → rcoef (R k) (J k) = 0 := by
          intro k h1 h2; simp [rcoef, h1, hR k, h2]
        rcases hA with (hA | hA) | hA
        · exact ⟨0, mem_univ _, hk 0 (by simpa using hA.1) hA.2⟩
        · exact ⟨1, mem_univ _, hk 1 (by simpa using hA.1) hA.2⟩
        · exact ⟨2, mem_univ _, hk 2 (by simpa using hA.1) hA.2⟩
      rw [hz, zero_mul]
      apply Finset.sum_eq_zero; intro e _
      apply Finset.sum_eq_zero; intro s _
      simp
  have : ∑ e : Fin 8, ∑ s : Fin 8, board o e s * star (board o' (e ^^^ δ) s) *
        ∏ k, R k (bit k e) (bit k (e ^^^ δ)) =
      ∑ J : Fin 3 → Fin 4, ∑ e : Fin 8, ∑ s : Fin 8,
        board o e s * star (board o' (e ^^^ δ) s) * ((∏ k, rcoef (R k) (J k)) *
          ∏ k, (rowW (J k) (bit k e) (bit k (e ^^^ δ)) : ℂ)) := by
    simp_rw [hexp, Finset.mul_sum]
    conv_lhs => arg 2; ext e; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [this]; simp only [hterm]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hc : o = o' ∧ δ = 0
  · simp only [hc, and_self, and_true]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 3 → Fin 4)]
    simp only [mem_univ, ite_true]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [rcoef, hR k, hc.1]
  · simp [hc]

end PFUL.Counterexample
