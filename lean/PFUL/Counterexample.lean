/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# H.12: the purification conjecture is false (finite-dimensional ancillas)

We formalise Theorem H.12.1 of `paper/lift.md`:

* `board_mem_unitaryGroup` : every board `U_o = Hd · diag(i^{m_o}) · Hd` is unitary;
* `isPure_Vsb` : for **all** finite ancilla types `a k` (in `Type`) and **all** local unitaries
  `A k : I_k ⊗ a_k → O_k ⊗ a_k`, the composed map `P ⊗ a → F ⊗ a` is unitary
  (multilinear reduction proved in general; the 125 slot checks by kernel computation);
* `valid_pcl` : the induced classical process is valid for all local stochastic interventions;
* `pcl_not_mem_convexHull` : it is not in the convex hull of the process functions;
* `purification_conjecture_false` : the combination.
-/
import PFUL.CounterexampleData
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Complex Matrix Finset

namespace PFUL.Counterexample

/-! ## Gaussian integers inside `ℂ` -/

/-- `x.1 + x.2 i`. -/
def toC (x : GI) : ℂ := (x.1 : ℂ) + (x.2 : ℂ) * I

@[simp] theorem toC_zero : toC 0 = 0 := by simp [toC]

theorem toC_add (x y : GI) : toC (x + y) = toC x + toC y := by
  simp only [toC, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem toC_mul (x y : GI) : toC (gmul x y) = toC x * toC y := by
  simp only [toC, gmul, Int.cast_sub, Int.cast_mul, Int.cast_add]
  ring_nf; rw [I_sq]; ring

theorem toC_gconj (x : GI) : toC (gconj x) = star (toC x) := by
  apply Complex.ext <;> simp [toC, gconj]

theorem toC_smul (n : ℤ) (x : GI) : toC (n • x) = (n : ℂ) * toC x := by
  simp only [toC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Int.cast_mul]; ring

/-- `toC` as an additive map. -/
def toCHom : GI →+ ℂ where
  toFun := toC
  map_zero' := toC_zero
  map_add' := toC_add

theorem toC_sum {ι : Type*} (s : Finset ι) (f : ι → GI) :
    toC (∑ i ∈ s, f i) = ∑ i ∈ s, toC (f i) :=
  map_sum toCHom f s

theorem toC_ipow (n : ℕ) (hn : n < 4) : toC (ipow n) = I ^ n := by
  interval_cases n <;> simp [toC, ipow, pow_succ]

/-! ## The boards -/

/-- The 3-qubit Hadamard, `Hd[x,z] = (-1)^{x·z}/√8`. -/
noncomputable def Hd : Matrix (Fin 8) (Fin 8) ℂ := fun x z => (sgn x z : ℂ) / (Real.sqrt 8 : ℂ)

/-- The board `U_o = Hd · diag(i^{m_o(z)}) · Hd` of H.12. -/
noncomputable def board (o : Fin 8) : Matrix (Fin 8) (Fin 8) ℂ :=
  Hd * Matrix.diagonal (fun z => I ^ mExp o z) * Hd

theorem sqrt8_sq : ((Real.sqrt 8 : ℂ)) * (Real.sqrt 8 : ℂ) = 8 := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem board_apply (o e s : Fin 8) : board o e s = toC (tab o e s) / 8 := by
  rw [← U8_eq_tab, U8, toC_sum, Finset.sum_div]
  simp only [board, Matrix.mul_apply, Matrix.diagonal_apply, Hd, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, toC_smul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [toC_ipow _ (mExp_lt o z), ← sgn_mul_sgn e z s]
  have h8 := sqrt8_sq
  have h0 : (Real.sqrt 8 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h8; norm_num at h8
  rw [← h8]
  push_cast
  field_simp

/-- Goal (1): every board is unitary. -/
theorem board_mem_unitaryGroup (o : Fin 8) : board o ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext s s'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, board_apply]
  have := congrArg toC (board_gram o s s')
  rw [toC_sum] at this
  simp only [toC_mul, toC_gconj] at this
  calc ∑ e, star (toC (tab o e s) / 8) * (toC (tab o e s') / 8)
      = (∑ e, star (toC (tab o e s)) * toC (tab o e s')) / 64 := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun e _ => ?_
        rw [star_div₀]; simp only [star_ofNat]; ring
    _ = _ := by
        rw [this]; split_ifs <;> simp [toC]

/-! ## Pure processes and the composition with local operations -/

/-- A process on three binary parties with past `P` and future `F`, as a matrix
`O ⊗ P → I ⊗ F` (rows `(i, f)`, columns `(o, π)`; strings are `Fin 8`). -/
abbrev Proc (P F : Type) := Matrix (Fin 8 × F) (Fin 8 × P) ℂ

/-- Link product of a process with local operations `A k : I_k ⊗ a_k → O_k ⊗ a_k`
(rows `(o_k, a'_k)`, columns `(i_k, a_k)`): the induced map `P ⊗ a → F ⊗ a`. -/
def compose {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) {a : Fin 3 → Type}
    (A : ∀ k, Matrix (Bool × a k) (Bool × a k) ℂ) :
    Matrix (F × (∀ k, a k)) (P × (∀ k, a k)) ℂ :=
  fun φβ πα => ∑ o : Fin 8, ∑ e : Fin 8,
    V (e, φβ.1) (o, πα.1) * ∏ k, A k (bit k o, φβ.2 k) (bit k e, πα.2 k)

/-- A process `P → F` (with `P`, `F` of the same type) is *pure* if composing it with arbitrary
local unitaries on arbitrary finite ancillas always gives a unitary. -/
def IsPure {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (a : Fin 3 → Type) [∀ k, Fintype (a k)] [∀ k, DecidableEq (a k)]
    (A : ∀ k, Matrix (Bool × a k) (Bool × a k) ℂ),
    (∀ k, A k ∈ Matrix.unitaryGroup (Bool × a k) ℂ) →
      compose V A ∈ Matrix.unitaryGroup (P × (∀ k, a k)) ℂ

/-- The classical process induced by a process and a source state `ψ ∈ P`:
`p(i|o) = Σ_f |⟨i, f| V |o, ψ⟩|²`. -/
noncomputable def inducedP {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) (ψ : P → ℂ)
    (i o : Fin 8) : ℝ :=
  ∑ φ : F, ‖∑ π : P, V (i, φ) (o, π) * ψ π‖ ^ 2

/-- A classical process `p(i|o)` is purifiable if it is induced by a pure process from a
normalised source state. -/
def Purifiable (p : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∃ (V : Proc (Fin 8 × Fin 8) (Fin 8 × Fin 8)) (ψ : Fin 8 × Fin 8 → ℂ),
    (∑ π, ‖ψ π‖ ^ 2) = 1 ∧ IsPure V ∧ p = inducedP V ψ

/-- The Switchboard `V|o,s,t⟩ = Σ_e U_o[e,s] |e⟩_I |o⟩_F |e ⊕ t⟩_F`. -/
noncomputable def Vsb : Proc (Fin 8 × Fin 8) (Fin 8 × Fin 8) :=
  fun r c => if r.2.1 = c.1 ∧ r.2.2 = r.1 ^^^ c.2.2 then board c.1 r.1 c.2.1 else 0

/-! ## The multilinear reduction -/

/-- Coefficients of a vector `b` with `Σ_o b[o,e,e'] = c [e = e']` in the slot basis. -/
noncomputable def coef (b : Bool → Bool → Bool → ℂ) (c : ℂ) (j : Fin 5) : ℂ :=
  if j = 0 then c else b false (slotX j) (slotY j) - (if slotX j = slotY j then c else 0)

theorem decomp (b : Bool → Bool → Bool → ℂ) (c : ℂ)
    (hb : ∀ y z, b false y z + b true y z = if y = z then c else 0) (x y z : Bool) :
    b x y z = ∑ j : Fin 5, coef b c j * (slotW j x y z : ℂ) := by
  rw [Fin.sum_univ_five]
  have h := hb y z
  cases x <;> cases y <;> cases z <;>
    simp [coef, slotW, slotX, slotY] at h ⊢ <;> linear_combination h

/-- `64 · T(J)` in `ℂ`, the scalar coefficient of the slot combination `J`. -/
theorem TC_eq (J : Fin 3 → Fin 5) (s s' δ : Fin 8) :
    ∑ o : Fin 8, ∑ e : Fin 8, star (board o e s) * board o (e ^^^ δ) s' *
        ∏ k, (slotW (J k) (bit k o) (bit k e) (bit k (e ^^^ δ)) : ℂ) =
      if J = 0 ∧ s = s' ∧ δ = 0 then 1 else 0 := by
  have h := congrArg toC (TD_eq J s s' δ)
  rw [TD, toC_sum] at h
  simp only [toC_sum] at h
  have key : ∀ o e, toC (if W J o e (e ^^^ δ) = 0 then 0 else
      W J o e (e ^^^ δ) • gmul (gconj (tab o e s)) (tab o (e ^^^ δ) s')) =
      64 * (star (board o e s) * board o (e ^^^ δ) s' *
        ∏ k, (slotW (J k) (bit k o) (bit k e) (bit k (e ^^^ δ)) : ℂ)) := by
    intro o e
    have hw : (if W J o e (e ^^^ δ) = 0 then (0 : GI) else
        W J o e (e ^^^ δ) • gmul (gconj (tab o e s)) (tab o (e ^^^ δ) s')) =
        W J o e (e ^^^ δ) • gmul (gconj (tab o e s)) (tab o (e ^^^ δ) s') := by
      split_ifs with h0 <;> simp [h0]
    rw [hw, toC_smul, toC_mul, toC_gconj, board_apply, board_apply, Fin.prod_univ_three, W]
    rw [star_div₀]; simp only [star_ofNat]; push_cast; ring
  simp only [key, ← Finset.mul_sum] at h
  have h64 : (64 : ℂ) ≠ 0 := by norm_num
  split_ifs at h ⊢ with hc
  · rw [show toC ((64 : ℤ), (0 : ℤ)) = 64 by simp [toC]] at h
    exact (mul_eq_left₀ h64).1 h
  · rw [toC_zero] at h
    exact (mul_eq_zero.1 h).resolve_left h64

/-- The scalar heart of purity: the multilinear form evaluated on vectors obeying the
unitarity constraint `Σ_o b_k[o,e,e'] = c_k [e = e']`. -/
theorem scalar_key (b : Fin 3 → Bool → Bool → Bool → ℂ) (c : Fin 3 → ℂ)
    (hb : ∀ k y z, b k false y z + b k true y z = if y = z then c k else 0) (s s' δ : Fin 8) :
    ∑ o : Fin 8, ∑ e : Fin 8, star (board o e s) * board o (e ^^^ δ) s' *
        ∏ k, b k (bit k o) (bit k e) (bit k (e ^^^ δ)) =
      if s = s' ∧ δ = 0 then ∏ k, c k else 0 := by
  have hexp : ∀ o e, ∏ k, b k (bit k o) (bit k e) (bit k (e ^^^ δ)) =
      ∑ J : Fin 3 → Fin 5, (∏ k, coef (b k) (c k) (J k)) *
        ∏ k, (slotW (J k) (bit k o) (bit k e) (bit k (e ^^^ δ)) : ℂ) := by
    intro o e
    simp_rw [fun k => decomp (b k) (c k) (hb k)]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (t := (Finset.univ : Finset (Fin 3 → Fin 5)))]
  have : ∀ J : Fin 3 → Fin 5, ∑ e : Fin 8, ∑ o : Fin 8, star (board o e s) * board o (e ^^^ δ) s' *
      ((∏ k, coef (b k) (c k) (J k)) *
        ∏ k, (slotW (J k) (bit k o) (bit k e) (bit k (e ^^^ δ)) : ℂ)) =
      (∏ k, coef (b k) (c k) (J k)) * (if J = 0 ∧ s = s' ∧ δ = 0 then 1 else 0) := by
    intro J
    rw [Finset.sum_comm, ← TC_eq J s s' δ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [Finset.sum_congr rfl fun J _ => this J]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hc : s = s' ∧ δ = 0
  · simp only [hc, and_self, and_true, if_true]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 3 → Fin 5)]
    simp [coef]
  · simp [hc]

/-- Closed form of the composed map for the Switchboard. -/
theorem compose_Vsb_apply {a : Fin 3 → Type} (A : ∀ k, Matrix (Bool × a k) (Bool × a k) ℂ)
    (o' u s t : Fin 8) (β α : ∀ k, a k) :
    compose Vsb A ((o', u), β) ((s, t), α) =
      board o' (u ^^^ t) s * ∏ k, A k (bit k o', β k) (bit k (u ^^^ t), α k) := by
  simp only [compose, Vsb]
  simp_rw [xor_eq_iff' u, ite_and, ite_mul, zero_mul]
  rw [Finset.sum_eq_single o']
  · rw [Finset.sum_eq_single (u ^^^ t)]
    · simp
    · intro e _ he; simp [he]
    · simp
  · intro o _ ho; simp [Ne.symm ho]
  · simp

/-- Goal (2): the H.12 Switchboard is pure, for all finite ancillas. -/
theorem isPure_Vsb : IsPure Vsb := by
  intro a _ _ A hA
  rw [Matrix.mem_unitaryGroup_iff']
  ext ⟨⟨s, t⟩, α⟩ ⟨⟨s', t'⟩, α'⟩
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, Fintype.sum_prod_type, compose_Vsb_apply]
  -- unitarity of each local operation, entrywise
  set B : Fin 3 → Bool → Bool → Bool → ℂ := fun k x y z =>
    ∑ b : a k, star (A k (x, b) (y, α k)) * A k (x, b) (z, α' k) with hBdef
  have hB : ∀ k y z, B k false y z + B k true y z =
      if y = z then (if α k = α' k then 1 else 0) else 0 := by
    intro k y z
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 (hA k)) (y, α k)) (z, α' k)
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool] at this
    simp only [Matrix.star_apply, Prod.mk.injEq] at this
    rw [hBdef]; simp only; rw [add_comm, this]
    split_ifs <;> simp_all
  have hstep : ∀ o' u, ∑ β : ∀ k, a k,
      star (board o' (u ^^^ t) s * ∏ k, A k (bit k o', β k) (bit k (u ^^^ t), α k)) *
        (board o' (u ^^^ t') s' * ∏ k, A k (bit k o', β k) (bit k (u ^^^ t'), α' k)) =
      star (board o' (u ^^^ t) s) * board o' ((u ^^^ t) ^^^ (t ^^^ t')) s' *
        ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k ((u ^^^ t) ^^^ (t ^^^ t'))) := by
    intro o' u
    rw [← xor_shift u t t']
    simp only [hBdef]
    rw [Fintype.prod_sum (fun k b => star (A k (bit k o', b) (bit k (u ^^^ t), α k)) *
      A k (bit k o', b) (bit k (u ^^^ t'), α' k)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [star_mul, star_prod, Finset.prod_mul_distrib]
    ring
  simp_rw [hstep]
  have hre : ∀ o', ∑ u : Fin 8, star (board o' (u ^^^ t) s) *
      board o' ((u ^^^ t) ^^^ (t ^^^ t')) s' *
        ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k ((u ^^^ t) ^^^ (t ^^^ t'))) =
      ∑ e : Fin 8, star (board o' e s) * board o' (e ^^^ (t ^^^ t')) s' *
        ∏ k, B k (bit k o') (bit k e) (bit k (e ^^^ (t ^^^ t'))) := by
    intro o'
    exact Fintype.sum_equiv (Function.Involutive.toPerm (fun u => u ^^^ t)
      (fun u => xor_xor_cancel' u t)) _ _ (fun u => rfl)
  simp_rw [hre]
  rw [scalar_key B _ hB s s' (t ^^^ t')]
  simp only [xor_eq_zero_iff', Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, Prod.mk.injEq]
  have hα : (∀ k, α k = α' k) ↔ α = α' := funext_iff.symm
  simp only [hα]
  by_cases h1 : s = s' <;> by_cases h2 : t = t' <;> by_cases h3 : α = α' <;> simp [h1, h2, h3]

/-! ## The classical process -/

/-- The source state `φ = (|011⟩ + e^{-iπ/4} |100⟩)/√2`. -/
noncomputable def phiSrc (s : Fin 8) : ℂ :=
  if s = 3 then 1 / (Real.sqrt 2 : ℂ)
  else if s = 4 then Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt 2 : ℂ) else 0

/-- The full source `φ ⊗ |0⟩_T`. -/
noncomputable def psiSrc (π : Fin 8 × Fin 8) : ℂ := if π.2 = 0 then phiSrc π.1 else 0

/-- The classical process `p(i|o) = |⟨i| U_o φ⟩|²`. -/
noncomputable def pcl (i o : Fin 8) : ℝ := ‖(board o *ᵥ phiSrc) i‖ ^ 2

theorem exp_neg_pi_four : Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * I) / (Real.sqrt 2 : ℂ) =
    (1 - I) / 2 := by
  rw [← ofReal_neg, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  field_simp
  push_cast
  ring

theorem norm_sq_key (a b c d : ℝ) :
    ‖((a + b * I) / 8) * (1 / (Real.sqrt 2 : ℂ)) + ((c + d * I) / 8) * ((1 - I) / 2)‖ ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + (a * c + b * d + (a * d - b * c)) * Real.sqrt 2) / 128 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hz : ((a + b * I) / 8) * (1 / (Real.sqrt 2 : ℂ)) + ((c + d * I) / 8) * ((1 - I) / 2) =
      ((a * Real.sqrt 2 / 16 + (c + d) / 16 : ℝ) : ℂ) +
        ((b * Real.sqrt 2 / 16 + (d - c) / 16 : ℝ) : ℂ) * I := by
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; exact hs0
    have h2' : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    field_simp
    push_cast
    ring_nf
    rw [I_sq]
    have : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by rw [sq, h2']
    rw [this]
    ring
  rw [hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  ring_nf
  rw [hs]
  ring

theorem pcl_eq (i o : Fin 8) : pcl i o = ((pN i o : ℝ) + (pM i o : ℝ) * Real.sqrt 2) / 128 := by
  have hv : (board o *ᵥ phiSrc) i = board o i 3 * (1 / (Real.sqrt 2 : ℂ)) +
      board o i 4 * ((1 - I) / 2) := by
    simp only [Matrix.mulVec, dotProduct, phiSrc, Fin.sum_univ_eight]
    rw [exp_neg_pi_four]
    simp
  rw [pcl, hv, board_apply, board_apply]
  have := norm_sq_key ((tab o i 3).1) ((tab o i 3).2) ((tab o i 4).1) ((tab o i 4).2)
  simp only [toC]
  push_cast at this ⊢
  rw [this, pN, pM]
  push_cast
  ring

/-- A classical process on three binary parties is *valid* if it is non-negative and gives
total probability 1 under every local stochastic intervention `q k (i_k) (o_k)`. -/
def Valid (p : Fin 8 → Fin 8 → ℝ) : Prop :=
  (∀ i o, 0 ≤ p i o) ∧
    ∀ q : Fin 3 → Bool → Bool → ℝ, (∀ k x y, 0 ≤ q k x y) → (∀ k x, q k x false + q k x true = 1) →
      ∑ i : Fin 8, ∑ o : Fin 8, p i o * ∏ k, q k (bit k i) (bit k o) = 1

theorem pcl_det (F : Fin 3 → Bool × Bool) : ∑ i : Fin 8, pcl i (applyF F i) = 1 := by
  obtain ⟨h1, h2⟩ := valid_det F
  simp_rw [pcl_eq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have e1 : (∑ i : Fin 8, (pN i (applyF F i) : ℝ)) = 128 := by exact_mod_cast h1
  have e2 : (∑ i : Fin 8, (pM i (applyF F i) : ℝ)) = 0 := by exact_mod_cast h2
  rw [e1, e2]; norm_num

theorem stoch_decomp (q : Bool → Bool → ℝ) (hq : ∀ x, q x false + q x true = 1) (x y : Bool) :
    q x y = ∑ f : Bool × Bool, q false f.1 * q true f.2 * (if loc f x = y then 1 else 0) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  have h0 := hq false; have h1 := hq true
  cases x <;> cases y <;> simp [loc] <;>
    first
    | linear_combination (q false false) * h1 | linear_combination -(q false false) * h1
    | linear_combination (q false true) * h1 | linear_combination -(q false true) * h1
    | linear_combination (q true false) * h0 | linear_combination -(q true false) * h0
    | linear_combination (q true true) * h0 | linear_combination -(q true true) * h0

/-- Goal (3): the induced classical process is valid. -/
theorem valid_pcl : Valid pcl := by
  refine ⟨fun i o => by unfold pcl; positivity, fun q _ hq => ?_⟩
  have hexp : ∀ i o : Fin 8, ∏ k, q k (bit k i) (bit k o) =
      ∑ F : Fin 3 → Bool × Bool, (∏ k, (q k false (F k).1 * q k true (F k).2)) *
        (if applyF F i = o then 1 else 0) := by
    intro i o
    simp_rw [fun k => stoch_decomp (q k) (hq k) (bit k i) (bit k o)]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, Finset.prod_boole,
      Finset.mem_univ, true_implies]
    refine Finset.sum_congr rfl fun F _ => ?_
    congr 1
    have : (∀ k, loc (F k) (bit k i) = bit k o) ↔ applyF F i = o := by
      rw [eq_comm, applyF, eq_ofBits_iff]
      constructor
      · intro h; exact ⟨(h 0).symm, (h 1).symm, (h 2).symm⟩
      · rintro ⟨h0, h1, h2⟩ k; fin_cases k
        · exact h0.symm
        · exact h1.symm
        · exact h2.symm
    simp only [this]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (t := (Finset.univ : Finset (Fin 3 → Bool × Bool)))]
  rw [Finset.sum_comm]
  have : ∀ F : Fin 3 → Bool × Bool, ∑ o : Fin 8, ∑ i : Fin 8,
      pcl i o * ((∏ k, (q k false (F k).1 * q k true (F k).2)) *
        (if applyF F i = o then 1 else 0)) = ∏ k, (q k false (F k).1 * q k true (F k).2) := by
    intro F
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, pcl_det, one_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 8)))
    (t := (Finset.univ : Finset (Fin 3 → Bool × Bool))), Finset.sum_congr rfl fun F _ => this F]
  rw [← Fintype.prod_sum (fun k (f : Bool × Bool) => q k false f.1 * q k true f.2)]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Fintype.sum_bool, Fintype.sum_bool,
    add_comm (q k false true), hq, add_comm (q k true true), hq]; ring

/-! ## Process functions and the separating inequality -/

/-- A process function: a map `w : O → I` with a unique fixed point `o = f(w(o))` for every
local deterministic intervention `f`. -/
def IsPF (w : Fin 8 → Fin 8) : Prop := ∀ F : Fin 3 → Bool × Bool, ∃! o, applyF F (w o) = o

/-- The classical process `p(i|o) = [w(o) = i]` of a process function. -/
def pfPoint (w : Fin 8 → Fin 8) (i o : Fin 8) : ℝ := if w o = i then 1 else 0

/-- The set of process-function points. -/
def PFset : Set (Fin 8 → Fin 8 → ℝ) := {x | ∃ w, IsPF w ∧ x = pfPoint w}

/-- The separating functional `L(x) = Σ g(i,o) x(i,o)`. -/
def Lg (x : Fin 8 → Fin 8 → ℝ) : ℝ := ∑ i : Fin 8, ∑ o : Fin 8, (gCoef i o : ℝ) * x i o

theorem Lg_pfPoint (w : Fin 8 → Fin 8) :
    Lg (pfPoint w) = gCoef (w 0) 0 + gCoef (w 1) 1 + gCoef (w 2) 2 + gCoef (w 4) 4 +
      gCoef (w 6) 6 := by
  rw [Lg, Finset.sum_comm]
  simp only [pfPoint, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fin.sum_univ_eight]
  have h3 := (gCoef_zero_cols (w 3)).1
  have h5 := (gCoef_zero_cols (w 5)).2.1
  have h7 := (gCoef_zero_cols (w 7)).2.2
  push_cast [h3, h5, h7]
  ring_nf

theorem IsPF.not_two {w : Fin 8 → Fin 8} (hw : IsPF w) (F : Fin 3 → Bool × Bool) {a b : Fin 8}
    (hab : a ≠ b) (ha : applyF F (w a) = a) (hb : applyF F (w b) = b) : False := by
  obtain ⟨x, -, hx⟩ := hw F
  exact hab ((hx a ha).trans (hx b hb).symm)

/-- Goal (4a): the separating inequality holds on every process function. -/
theorem Lg_nonneg_of_isPF {w : Fin 8 → Fin 8} (hw : IsPF w) : 0 ≤ Lg (pfPoint w) := by
  rw [Lg_pfPoint]
  have h := all_finRange (all_finRange (all_finRange (all_finRange (all_finRange pfCheck_eq
    (w 0)) (w 1)) (w 2)) (w 4)) (w 6)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨F, -, hF⟩
  · exact_mod_cast h
  · exfalso
    rcases two_cases _ _ _ _ _ hF with h | h | h | h | h | h | h | h | h | h <;>
    · simp only [beq_iff_eq] at h
      exact hw.not_two F (by decide) h.1 h.2

theorem Lg_pcl : Lg pcl = (32 - 24 * Real.sqrt 2) / 128 := by
  simp only [Lg, pcl_eq]
  have e1 : (∑ i : Fin 8, ∑ o : Fin 8, (gCoef i o : ℝ) * pN i o) = 32 := by exact_mod_cast g_pN
  have e2 : (∑ i : Fin 8, ∑ o : Fin 8, (gCoef i o : ℝ) * pM i o) = -24 := by exact_mod_cast g_pM
  have : ∀ i o : Fin 8, (gCoef i o : ℝ) * (((pN i o : ℝ) + (pM i o : ℝ) * Real.sqrt 2) / 128) =
      ((gCoef i o : ℝ) * pN i o) / 128 + ((gCoef i o : ℝ) * pM i o) * Real.sqrt 2 / 128 := by
    intro i o; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => this i o]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  rw [e1, e2]
  ring

theorem Lg_pcl_neg : Lg pcl < 0 := by
  rw [Lg_pcl]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have : 4 / 3 < Real.sqrt 2 := by nlinarith
  linarith

/-- Goal (4b): the induced process is outside the convex hull of the process functions. -/
theorem pcl_not_mem_convexHull : pcl ∉ convexHull ℝ PFset := by
  intro hp
  have hconv : Convex ℝ {x : Fin 8 → Fin 8 → ℝ | 0 ≤ Lg x} := by
    refine convex_halfSpace_ge ?_ 0
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · simp only [Lg, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Lg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => ?_
      ring
  have hsub : PFset ⊆ {x | 0 ≤ Lg x} := by
    rintro x ⟨w, hw, rfl⟩; exact Lg_nonneg_of_isPF hw
  have := convexHull_min hsub hconv hp
  exact absurd (Lg_pcl_neg) (not_lt.2 this)

/-! ## The purification -/

theorem norm_psiSrc : (∑ π : Fin 8 × Fin 8, ‖psiSrc π‖ ^ 2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [psiSrc]
  have : ∀ x : Fin 8, (∑ y : Fin 8, ‖if y = 0 then phiSrc x else 0‖ ^ 2) = ‖phiSrc x‖ ^ 2 := by
    intro x
    rw [Finset.sum_eq_single 0]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  simp_rw [this]
  simp only [phiSrc, Fin.sum_univ_eight]
  rw [exp_neg_pi_four]
  simp
  have h1 : ‖(1 : ℂ) - I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; norm_num
  rw [div_pow, h1]; norm_num

theorem inducedP_Vsb : pcl = inducedP Vsb psiSrc := by
  funext i o
  simp only [inducedP, pcl, Fintype.sum_prod_type, Vsb, psiSrc]
  have inner : ∀ o' u : Fin 8, (∑ s : Fin 8, ∑ t : Fin 8,
      (if o' = o ∧ u = i ^^^ t then board o i s else 0) * (if t = 0 then phiSrc s else 0)) =
      if o' = o ∧ u = i then (board o *ᵥ phiSrc) i else 0 := by
    intro o' u
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_ite_eq' Finset.univ (0 : Fin 8) _]
    simp only [Finset.mem_univ, if_true, xor_zero']
    split_ifs with h
    · simp [Matrix.mulVec, dotProduct]
    · simp
  simp_rw [inner]
  rw [Finset.sum_eq_single o]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro u _ hu; simp [hu]
    · simp
  · intro o' _ ho; simp [ho]
  · simp

theorem purifiable_pcl : Purifiable pcl :=
  ⟨Vsb, psiSrc, norm_psiSrc, isPure_Vsb, inducedP_Vsb⟩

/-- **Theorem H.12.1** (finite-dimensional ancillas). There is a valid three-party binary
classical process that is purifiable but is not a mixture of process functions. -/
theorem purification_conjecture_false :
    ∃ p : Fin 8 → Fin 8 → ℝ, Valid p ∧ Purifiable p ∧ p ∉ convexHull ℝ PFset :=
  ⟨pcl, valid_pcl, purifiable_pcl, pcl_not_mem_convexHull⟩

end PFUL.Counterexample
