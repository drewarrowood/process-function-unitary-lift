/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# H.12 counterexample: exact integer data and kernel-checked computations

All data of the H.12 machine is encoded with integers (Gaussian integers as pairs `ℤ × ℤ`).
Every finite check below is a closed `Bool` computation evaluated by the Lean *kernel*
(`decide +kernel`), so no `native_decide` / `Lean.ofReduceBool` is involved.

Conventions (as in `verify_h12/verify.py`): a 3-bit string is an element of `Fin 8`;
party `k : Fin 3` owns bit `2 - k` (party 0 is the most significant bit).
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.FinCases

namespace PFUL.Counterexample

/-- Gaussian integers `x.1 + x.2 i`, as pairs (additive structure is the product one). -/
abbrev GI := ℤ × ℤ

/-- Gaussian-integer multiplication. -/
def gmul (x y : GI) : GI := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Gaussian-integer conjugation. -/
def gconj (x : GI) : GI := (x.1, -x.2)

/-- `i ^ n` for `n < 4`. -/
def ipow (n : ℕ) : GI :=
  if n = 0 then (1, 0) else if n = 1 then (0, 1) else if n = 2 then (-1, 0) else (0, -1)

/-- The exponent table `m_o(z)` of H.12 (row `o`, column `z`). -/
def mTab : List (List ℕ) :=
  [[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],
   [0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]

/-- `m_o(z)`. -/
def mExp (o z : Fin 8) : ℕ := (mTab.getD o.val []).getD z.val 0

/-- Bit of party `k` in a 3-bit string. -/
def bit (k : Fin 3) (x : Fin 8) : Bool := x.val.testBit (2 - k.val)

/-- The 3-bit string with bits `a b c` (party 0 first). -/
def ofBits (a b c : Bool) : Fin 8 :=
  ⟨4 * a.toNat + 2 * b.toNat + c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

/-- `(-1)^{z · x}`. -/
def sgn (z x : Fin 8) : ℤ :=
  if xor (xor (bit 0 z && bit 0 x) (bit 1 z && bit 1 x)) (bit 2 z && bit 2 x) then -1 else 1

/-- `8 U_o[e,s] = Σ_z (-1)^{z·(e ⊕ s)} i^{m_o(z)}`. -/
def U8 (o e s : Fin 8) : GI := ∑ z : Fin 8, sgn z (e ^^^ s) • ipow (mExp o z)

def boardTab : List (List (List (ℤ × ℤ))) :=
  [[[(4,-2), (-2,0), (-2,0), (0,2), (2,0), (4,2), (0,-2), (2,0)], [(-2,0), (4,-2), (0,2), (-2,0), (4,2), (2,0), (2,0), (0,-2)], [(-2,0), (0,2), (4,-2), (-2,0), (0,-2), (2,0), (2,0), (4,2)], [(0,2), (-2,0), (-2,0), (4,-2), (2,0), (0,-2), (4,2), (2,0)], [(2,0), (4,2), (0,-2), (2,0), (4,-2), (-2,0), (-2,0), (0,2)], [(4,2), (2,0), (2,0), (0,-2), (-2,0), (4,-2), (0,2), (-2,0)], [(0,-2), (2,0), (2,0), (4,2), (-2,0), (0,2), (4,-2), (-2,0)], [(2,0), (0,-2), (4,2), (2,0), (0,2), (-2,0), (-2,0), (4,-2)]],
   [[(0,-2), (-2,0), (2,0), (0,2), (-2,0), (4,2), (4,-2), (2,0)], [(-2,0), (0,-2), (0,2), (2,0), (4,2), (-2,0), (2,0), (4,-2)], [(2,0), (0,2), (0,-2), (-2,0), (4,-2), (2,0), (-2,0), (4,2)], [(0,2), (2,0), (-2,0), (0,-2), (2,0), (4,-2), (4,2), (-2,0)], [(-2,0), (4,2), (4,-2), (2,0), (0,-2), (-2,0), (2,0), (0,2)], [(4,2), (-2,0), (2,0), (4,-2), (-2,0), (0,-2), (0,2), (2,0)], [(4,-2), (2,0), (-2,0), (4,2), (2,0), (0,2), (0,-2), (-2,0)], [(2,0), (4,-2), (4,2), (-2,0), (0,2), (2,0), (-2,0), (0,-2)]],
   [[(2,0), (0,-2), (-2,0), (0,2), (4,-2), (2,4), (0,-2), (2,0)], [(0,-2), (2,0), (0,2), (-2,0), (2,4), (4,-2), (2,0), (0,-2)], [(-2,0), (0,2), (2,0), (0,-2), (0,-2), (2,0), (4,-2), (2,4)], [(0,2), (-2,0), (0,-2), (2,0), (2,0), (0,-2), (2,4), (4,-2)], [(4,-2), (2,4), (0,-2), (2,0), (2,0), (0,-2), (-2,0), (0,2)], [(2,4), (4,-2), (2,0), (0,-2), (0,-2), (2,0), (0,2), (-2,0)], [(0,-2), (2,0), (4,-2), (2,4), (-2,0), (0,2), (2,0), (0,-2)], [(2,0), (0,-2), (2,4), (4,-2), (0,2), (-2,0), (0,-2), (2,0)]],
   [[(-2,0), (0,-2), (2,0), (0,2), (0,-2), (2,4), (4,-2), (2,0)], [(0,-2), (-2,0), (0,2), (2,0), (2,4), (0,-2), (2,0), (4,-2)], [(2,0), (0,2), (-2,0), (0,-2), (4,-2), (2,0), (0,-2), (2,4)], [(0,2), (2,0), (0,-2), (-2,0), (2,0), (4,-2), (2,4), (0,-2)], [(0,-2), (2,4), (4,-2), (2,0), (-2,0), (0,-2), (2,0), (0,2)], [(2,4), (0,-2), (2,0), (4,-2), (0,-2), (-2,0), (0,2), (2,0)], [(4,-2), (2,0), (0,-2), (2,4), (2,0), (0,2), (-2,0), (0,-2)], [(2,0), (4,-2), (2,4), (0,-2), (0,2), (2,0), (0,-2), (-2,0)]],
   [[(-4,2), (2,0), (2,0), (0,-2), (2,0), (0,-2), (4,2), (2,0)], [(2,0), (-4,2), (0,-2), (2,0), (0,-2), (2,0), (2,0), (4,2)], [(2,0), (0,-2), (-4,2), (2,0), (4,2), (2,0), (2,0), (0,-2)], [(0,-2), (2,0), (2,0), (-4,2), (2,0), (4,2), (0,-2), (2,0)], [(2,0), (0,-2), (4,2), (2,0), (-4,2), (2,0), (2,0), (0,-2)], [(0,-2), (2,0), (2,0), (4,2), (2,0), (-4,2), (0,-2), (2,0)], [(4,2), (2,0), (2,0), (0,-2), (2,0), (0,-2), (-4,2), (2,0)], [(2,0), (4,2), (0,-2), (2,0), (0,-2), (2,0), (2,0), (-4,2)]],
   [[(0,2), (2,0), (-2,0), (0,-2), (6,0), (0,-2), (0,2), (2,0)], [(2,0), (0,2), (0,-2), (-2,0), (0,-2), (6,0), (2,0), (0,2)], [(-2,0), (0,-2), (0,2), (2,0), (0,2), (2,0), (6,0), (0,-2)], [(0,-2), (-2,0), (2,0), (0,2), (2,0), (0,2), (0,-2), (6,0)], [(6,0), (0,-2), (0,2), (2,0), (0,2), (2,0), (-2,0), (0,-2)], [(0,-2), (6,0), (2,0), (0,2), (2,0), (0,2), (0,-2), (-2,0)], [(0,2), (2,0), (6,0), (0,-2), (-2,0), (0,-2), (0,2), (2,0)], [(2,0), (0,2), (0,-2), (6,0), (0,-2), (-2,0), (2,0), (0,2)]],
   [[(-2,0), (0,2), (2,0), (0,-2), (0,2), (2,-4), (4,2), (2,0)], [(0,2), (-2,0), (0,-2), (2,0), (2,-4), (0,2), (2,0), (4,2)], [(2,0), (0,-2), (-2,0), (0,2), (4,2), (2,0), (0,2), (2,-4)], [(0,-2), (2,0), (0,2), (-2,0), (2,0), (4,2), (2,-4), (0,2)], [(0,2), (2,-4), (4,2), (2,0), (-2,0), (0,2), (2,0), (0,-2)], [(2,-4), (0,2), (2,0), (4,2), (0,2), (-2,0), (0,-2), (2,0)], [(4,2), (2,0), (0,2), (2,-4), (2,0), (0,-2), (-2,0), (0,2)], [(2,0), (4,2), (2,-4), (0,2), (0,-2), (2,0), (0,2), (-2,0)]],
   [[(2,0), (0,2), (-2,0), (0,-2), (4,2), (2,-4), (0,2), (2,0)], [(0,2), (2,0), (0,-2), (-2,0), (2,-4), (4,2), (2,0), (0,2)], [(-2,0), (0,-2), (2,0), (0,2), (0,2), (2,0), (4,2), (2,-4)], [(0,-2), (-2,0), (0,2), (2,0), (2,0), (0,2), (2,-4), (4,2)], [(4,2), (2,-4), (0,2), (2,0), (2,0), (0,2), (-2,0), (0,-2)], [(2,-4), (4,2), (2,0), (0,2), (0,2), (2,0), (0,-2), (-2,0)], [(0,2), (2,0), (4,2), (2,-4), (-2,0), (0,-2), (2,0), (0,2)], [(2,0), (0,2), (2,-4), (4,2), (0,-2), (-2,0), (0,2), (2,0)]]]

/-- Table lookup of `8 U_o[e,s]` (row `o`, then `e`, then `s`). -/
def tab (o e s : Fin 8) : GI := ((boardTab.getD o.val []).getD e.val []).getD s.val (0, 0)

/-! ### Small helper for turning `List.all` checks into universal statements -/

theorem all_finRange {n : ℕ} {P : Fin n → Bool} (h : (List.finRange n).all P = true) (x : Fin n) :
    P x = true :=
  List.all_eq_true.1 h x (List.mem_finRange x)

/-! ### Bit lemmas (finite, by `decide`) -/

theorem bit_xor : ∀ (k : Fin 3) (x y : Fin 8), bit k (x ^^^ y) = xor (bit k x) (bit k y) := by
  decide

theorem eq_ofBits_iff : ∀ (o : Fin 8) (a b c : Bool),
    o = ofBits a b c ↔ bit 0 o = a ∧ bit 1 o = b ∧ bit 2 o = c := by
  decide

theorem xor_eq_iff' : ∀ u e t : Fin 8, u = e ^^^ t ↔ e = u ^^^ t := by decide

theorem xor_xor_cancel' : ∀ u t : Fin 8, (u ^^^ t) ^^^ t = u := by decide

theorem xor_shift : ∀ u t t' : Fin 8, u ^^^ t' = (u ^^^ t) ^^^ (t ^^^ t') := by decide

theorem xor_eq_zero_iff' : ∀ t t' : Fin 8, t ^^^ t' = 0 ↔ t = t' := by decide

theorem xor_zero' : ∀ t : Fin 8, t ^^^ 0 = t := by decide

theorem sgn_mul_sgn : ∀ e z s : Fin 8, sgn e z * sgn z s = sgn z (e ^^^ s) := by decide

theorem mExp_lt : ∀ o z : Fin 8, mExp o z < 4 := by decide

/-! ### (1) The table is the board formula, and every board is unitary -/

/-- `tab` agrees with the defining formula `U8`. -/
def tabCheck : Bool :=
  (List.finRange 8).all fun o => (List.finRange 8).all fun e => (List.finRange 8).all fun s =>
    U8 o e s == tab o e s

theorem tabCheck_eq : tabCheck = true := by decide +kernel

theorem U8_eq_tab (o e s : Fin 8) : U8 o e s = tab o e s := by
  have := all_finRange (all_finRange (all_finRange tabCheck_eq o) e) s
  simpa using this

/-- `(8U_o)^† (8U_o) = 64·1`, entrywise. -/
def unitaryCheck : Bool :=
  (List.finRange 8).all fun o => (List.finRange 8).all fun s => (List.finRange 8).all fun s' =>
    (∑ e : Fin 8, gmul (gconj (tab o e s)) (tab o e s')) ==
      (if s = s' then ((64 : ℤ), (0 : ℤ)) else 0)

theorem unitaryCheck_eq : unitaryCheck = true := by decide +kernel

theorem board_gram (o s s' : Fin 8) :
    (∑ e : Fin 8, gmul (gconj (tab o e s)) (tab o e s')) =
      (if s = s' then ((64 : ℤ), (0 : ℤ)) else 0) := by
  have := all_finRange (all_finRange (all_finRange unitaryCheck_eq o) s) s'
  simpa using this

/-! ### (2) The 125 multilinear purity checks

The four-dimensional space `N = {v : Σ_o v[o,e,e'] = 0}` and the vector `b0` give five
slot vectors `slotW j` (`j = 0` is `b0`, `j = 1 + 2x + y` is `v_{x,y}`). -/

/-- First index of a slot vector `v_{x,y}`. -/
def slotX (j : Fin 5) : Bool := decide (3 ≤ j.val)

/-- Second index of a slot vector `v_{x,y}`. -/
def slotY (j : Fin 5) : Bool := decide (j.val % 2 = 0)

/-- The five slot vectors: `b0[o,e,e'] = [o = 0][e = e']`,
`v_{x,y}[o,e,e'] = [e = x][e' = y] (-1)^o`. -/
def slotW (j : Fin 5) (o e e' : Bool) : ℤ :=
  if j = 0 then (if o = false ∧ e = e' then 1 else 0)
  else if e = slotX j ∧ e' = slotY j then (if o then -1 else 1) else 0

/-- The bit flip `e ⊕ e'` forced by a slot vector. -/
def dj (j : Fin 5) : Bool := if j = 0 then false else xor (slotX j) (slotY j)

theorem slotW_ne : ∀ (j : Fin 5) (o e e' : Bool), slotW j o e e' ≠ 0 → xor e e' = dj j := by
  decide

/-- Weight of a slot combination `J` at `(o, e, e')`. -/
def W (J : Fin 3 → Fin 5) (o e e' : Fin 8) : ℤ :=
  slotW (J 0) (bit 0 o) (bit 0 e) (bit 0 e') * slotW (J 1) (bit 1 o) (bit 1 e) (bit 1 e') *
    slotW (J 2) (bit 2 o) (bit 2 e) (bit 2 e')

/-- The flip string forced by `J`. -/
def δJ (J : Fin 3 → Fin 5) : Fin 8 := ofBits (dj (J 0)) (dj (J 1)) (dj (J 2))

/-- `64 T(J)[s,s'; δ]`, with zero weights skipped (the skip does not change the value). -/
def TD (J : Fin 3 → Fin 5) (s s' δ : Fin 8) : GI :=
  ∑ o : Fin 8, ∑ e : Fin 8, (if W J o e (e ^^^ δ) = 0 then 0 else
    W J o e (e ^^^ δ) • gmul (gconj (tab o e s)) (tab o (e ^^^ δ) s'))

/-- The slot combinations `(j0, j1, ·)`, each on its forced flip `δJ J`, all 64 entries
`(s,s')`. The 125 combinations are split into 25 blocks to keep kernel memory small. -/
def purityBlock (j0 j1 : Fin 5) : Bool :=
  (List.finRange 5).all fun j2 => (List.finRange 8).all fun s => (List.finRange 8).all fun s' =>
    TD ![j0, j1, j2] s s' (δJ ![j0, j1, j2]) ==
      (if j0 = 0 ∧ j1 = 0 ∧ j2 = 0 ∧ s = s' then ((64 : ℤ), (0 : ℤ)) else 0)

theorem purityBlock_0_0 : purityBlock 0 0 = true := by decide +kernel
theorem purityBlock_0_1 : purityBlock 0 1 = true := by decide +kernel
theorem purityBlock_0_2 : purityBlock 0 2 = true := by decide +kernel
theorem purityBlock_0_3 : purityBlock 0 3 = true := by decide +kernel
theorem purityBlock_0_4 : purityBlock 0 4 = true := by decide +kernel
theorem purityBlock_1_0 : purityBlock 1 0 = true := by decide +kernel
theorem purityBlock_1_1 : purityBlock 1 1 = true := by decide +kernel
theorem purityBlock_1_2 : purityBlock 1 2 = true := by decide +kernel
theorem purityBlock_1_3 : purityBlock 1 3 = true := by decide +kernel
theorem purityBlock_1_4 : purityBlock 1 4 = true := by decide +kernel
theorem purityBlock_2_0 : purityBlock 2 0 = true := by decide +kernel
theorem purityBlock_2_1 : purityBlock 2 1 = true := by decide +kernel
theorem purityBlock_2_2 : purityBlock 2 2 = true := by decide +kernel
theorem purityBlock_2_3 : purityBlock 2 3 = true := by decide +kernel
theorem purityBlock_2_4 : purityBlock 2 4 = true := by decide +kernel
theorem purityBlock_3_0 : purityBlock 3 0 = true := by decide +kernel
theorem purityBlock_3_1 : purityBlock 3 1 = true := by decide +kernel
theorem purityBlock_3_2 : purityBlock 3 2 = true := by decide +kernel
theorem purityBlock_3_3 : purityBlock 3 3 = true := by decide +kernel
theorem purityBlock_3_4 : purityBlock 3 4 = true := by decide +kernel
theorem purityBlock_4_0 : purityBlock 4 0 = true := by decide +kernel
theorem purityBlock_4_1 : purityBlock 4 1 = true := by decide +kernel
theorem purityBlock_4_2 : purityBlock 4 2 = true := by decide +kernel
theorem purityBlock_4_3 : purityBlock 4 3 = true := by decide +kernel
theorem purityBlock_4_4 : purityBlock 4 4 = true := by decide +kernel

theorem purityBlock_all : ∀ j0 j1 : Fin 5, purityBlock j0 j1 = true
  | ⟨0, _⟩, ⟨0, _⟩ => purityBlock_0_0
  | ⟨0, _⟩, ⟨1, _⟩ => purityBlock_0_1
  | ⟨0, _⟩, ⟨2, _⟩ => purityBlock_0_2
  | ⟨0, _⟩, ⟨3, _⟩ => purityBlock_0_3
  | ⟨0, _⟩, ⟨4, _⟩ => purityBlock_0_4
  | ⟨1, _⟩, ⟨0, _⟩ => purityBlock_1_0
  | ⟨1, _⟩, ⟨1, _⟩ => purityBlock_1_1
  | ⟨1, _⟩, ⟨2, _⟩ => purityBlock_1_2
  | ⟨1, _⟩, ⟨3, _⟩ => purityBlock_1_3
  | ⟨1, _⟩, ⟨4, _⟩ => purityBlock_1_4
  | ⟨2, _⟩, ⟨0, _⟩ => purityBlock_2_0
  | ⟨2, _⟩, ⟨1, _⟩ => purityBlock_2_1
  | ⟨2, _⟩, ⟨2, _⟩ => purityBlock_2_2
  | ⟨2, _⟩, ⟨3, _⟩ => purityBlock_2_3
  | ⟨2, _⟩, ⟨4, _⟩ => purityBlock_2_4
  | ⟨3, _⟩, ⟨0, _⟩ => purityBlock_3_0
  | ⟨3, _⟩, ⟨1, _⟩ => purityBlock_3_1
  | ⟨3, _⟩, ⟨2, _⟩ => purityBlock_3_2
  | ⟨3, _⟩, ⟨3, _⟩ => purityBlock_3_3
  | ⟨3, _⟩, ⟨4, _⟩ => purityBlock_3_4
  | ⟨4, _⟩, ⟨0, _⟩ => purityBlock_4_0
  | ⟨4, _⟩, ⟨1, _⟩ => purityBlock_4_1
  | ⟨4, _⟩, ⟨2, _⟩ => purityBlock_4_2
  | ⟨4, _⟩, ⟨3, _⟩ => purityBlock_4_3
  | ⟨4, _⟩, ⟨4, _⟩ => purityBlock_4_4
  | ⟨n + 5, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 5, h⟩ => absurd h (by omega)

theorem W_ne {J : Fin 3 → Fin 5} {o e δ : Fin 8} (h : W J o e (e ^^^ δ) ≠ 0) : δ = δJ J := by
  simp only [W, ne_eq, mul_eq_zero, not_or] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have k0 := slotW_ne _ _ _ _ h0
  have k1 := slotW_ne _ _ _ _ h1
  have k2 := slotW_ne _ _ _ _ h2
  rw [bit_xor] at k0 k1 k2
  rw [δJ, eq_ofBits_iff]
  refine ⟨?_, ?_, ?_⟩ <;> [rw [← k0]; rw [← k1]; rw [← k2]] <;>
    cases bit _ e <;> cases bit _ δ <;> rfl

theorem fin3_eta (J : Fin 3 → Fin 5) : ![J 0, J 1, J 2] = J := by
  funext k; fin_cases k <;> rfl

theorem TD_eq (J : Fin 3 → Fin 5) (s s' δ : Fin 8) :
    TD J s s' δ = if J = 0 ∧ s = s' ∧ δ = 0 then ((64 : ℤ), (0 : ℤ)) else 0 := by
  by_cases hδ : δ = δJ J
  · subst hδ
    have := all_finRange (all_finRange (all_finRange (purityBlock_all (J 0) (J 1)) (J 2)) s) s'
    rw [fin3_eta] at this
    have hJ : J = 0 ↔ J 0 = 0 ∧ J 1 = 0 ∧ J 2 = 0 := by
      constructor
      · rintro rfl; simp
      · rintro ⟨a, b, c⟩; funext k; fin_cases k <;> assumption
    have h0 : J = 0 → δJ J = 0 := by rintro rfl; rfl
    simp only [beq_iff_eq] at this
    rw [this]
    have hiff : (J 0 = 0 ∧ J 1 = 0 ∧ J 2 = 0 ∧ s = s') ↔ (J = 0 ∧ s = s' ∧ δJ J = 0) := by
      constructor
      · rintro ⟨a, b, c, d⟩
        have hJ0 := hJ.2 ⟨a, b, c⟩
        exact ⟨hJ0, d, h0 hJ0⟩
      · rintro ⟨a, d, -⟩
        exact ⟨(hJ.1 a).1, (hJ.1 a).2.1, (hJ.1 a).2.2, d⟩
    exact if_congr hiff rfl rfl
  · have hz : TD J s s' δ = 0 := by
      apply Finset.sum_eq_zero; intro o _
      apply Finset.sum_eq_zero; intro e _
      have : W J o e (e ^^^ δ) = 0 := by
        by_contra h; exact hδ (W_ne h)
      simp [this]
    rw [hz]
    have : ¬ (J = 0 ∧ s = s' ∧ δ = 0) := by
      rintro ⟨rfl, -, rfl⟩; exact hδ rfl
    simp [this]

/-! ### (3) The classical process `p = (pN + pM √2)/128` -/

/-- `128 p(i|o)`, rational part: `|8U_o[i,3]|² + |8U_o[i,4]|²`. -/
def pN (i o : Fin 8) : ℤ :=
  (tab o i 3).1 ^ 2 + (tab o i 3).2 ^ 2 + (tab o i 4).1 ^ 2 + (tab o i 4).2 ^ 2

/-- `128 p(i|o)`, coefficient of `√2`: `Re w + Im w`, `w = conj(8U_o[i,3]) 8U_o[i,4]`. -/
def pM (i o : Fin 8) : ℤ :=
  (tab o i 3).1 * (tab o i 4).1 + (tab o i 3).2 * (tab o i 4).2 +
    ((tab o i 3).1 * (tab o i 4).2 - (tab o i 3).2 * (tab o i 4).1)

/-- A local deterministic map `Bool → Bool`, given by its values `(f false, f true)`. -/
def loc (f : Bool × Bool) (x : Bool) : Bool := if x then f.2 else f.1

/-- The global deterministic intervention `i ↦ f(i)` built from three local maps. -/
def applyF (F : Fin 3 → Bool × Bool) (i : Fin 8) : Fin 8 :=
  ofBits (loc (F 0) (bit 0 i)) (loc (F 1) (bit 1 i)) (loc (F 2) (bit 2 i))

/-- The four local deterministic maps. -/
def locMaps : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_locMaps (f : Bool × Bool) : f ∈ locMaps := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> decide

/-- All 64 deterministic interventions give total probability exactly 1. -/
def validCheck : Bool :=
  locMaps.all fun f0 => locMaps.all fun f1 => locMaps.all fun f2 =>
    ((∑ i : Fin 8, pN i (applyF ![f0, f1, f2] i)) == 128) &&
      ((∑ i : Fin 8, pM i (applyF ![f0, f1, f2] i)) == 0)

theorem validCheck_eq : validCheck = true := by decide +kernel

theorem fin3_eta' (F : Fin 3 → Bool × Bool) : ![F 0, F 1, F 2] = F := by
  funext k; fin_cases k <;> rfl

theorem valid_det (F : Fin 3 → Bool × Bool) :
    (∑ i : Fin 8, pN i (applyF F i)) = 128 ∧ (∑ i : Fin 8, pM i (applyF F i)) = 0 := by
  have h := validCheck_eq
  simp only [validCheck, List.all_eq_true] at h
  have := h _ (mem_locMaps (F 0)) _ (mem_locMaps (F 1)) _ (mem_locMaps (F 2))
  rw [fin3_eta'] at this
  simpa using this

/-! ### (4) The separating inequality on process functions -/

/-- The integer inequality `g` (row `i`, column `o`), with constant `g0 = 0`. -/
def gTab : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0],
   [1, -1, 0, 0, 0, 0, 0, 0],
   [1, 0, -1, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, -1, 0, 0, 0],
   [2, 0, 0, 0, -1, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, -1, 0],
   [2, 0, 0, 0, 0, 0, 0, 0]]

/-- `g(i,o)`. -/
def gCoef (i o : Fin 8) : ℤ := (gTab.getD i.val []).getD o.val 0

theorem gCoef_zero_cols : ∀ i : Fin 8, gCoef i 3 = 0 ∧ gCoef i 5 = 0 ∧ gCoef i 7 = 0 := by
  decide

/-- `128 (g · p) = 32 - 24 √2`. -/
theorem g_pN : (∑ i : Fin 8, ∑ o : Fin 8, gCoef i o * pN i o) = 32 := by decide +kernel

theorem g_pM : (∑ i : Fin 8, ∑ o : Fin 8, gCoef i o * pM i o) = -24 := by decide +kernel

/-- The four interventions used to exclude violations (identity = `(false,true)`,
constant 0 = `(false,false)`). -/
def F4 : List (Fin 3 → Bool × Bool) :=
  [![(false, true), (false, true), (false, false)], ![(false, false), (false, false), (false, true)],
   ![(false, true), (false, true), (false, true)], ![(false, true), (false, false), (false, false)]]

/-- At least two of five booleans hold. -/
def two (b : List Bool) : Bool := decide (2 ≤ (b.filter id).length)

/-- For every assignment of `w` on the strings `000, 001, 010, 100, 110`, either the
inequality holds, or one of the interventions in `F4` has two fixed points among them. -/
def pfCheck : Bool :=
  (List.finRange 8).all fun v0 => (List.finRange 8).all fun v1 =>
  (List.finRange 8).all fun v2 => (List.finRange 8).all fun v4 => (List.finRange 8).all fun v6 =>
    decide (0 ≤ gCoef v0 0 + gCoef v1 1 + gCoef v2 2 + gCoef v4 4 + gCoef v6 6) ||
      F4.any fun F => two [applyF F v0 == 0, applyF F v1 == 1, applyF F v2 == 2,
        applyF F v4 == 4, applyF F v6 == 6]

theorem pfCheck_eq : pfCheck = true := by decide +kernel

theorem two_cases : ∀ b0 b1 b2 b3 b4 : Bool, two [b0, b1, b2, b3, b4] = true →
    (b0 ∧ b1) ∨ (b0 ∧ b2) ∨ (b0 ∧ b3) ∨ (b0 ∧ b4) ∨ (b1 ∧ b2) ∨ (b1 ∧ b3) ∨ (b1 ∧ b4) ∨
      (b2 ∧ b3) ∨ (b2 ∧ b4) ∨ (b3 ∧ b4) := by
  decide

end PFUL.Counterexample
