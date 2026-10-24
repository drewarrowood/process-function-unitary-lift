/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 12: the H.12 counterexample in the general process-matrix (Choi) framework

Bridges from the counterexample's own definitions (`Valid`, `IsPure`, `inducedP`, `PFset`) to
the AFNB process-matrix framework of `PFUL.ProcessMatrix` (general `W`, link product, CPTP
Choi matrices, all finite ancillas):

* `isValidPM_Wcl_iff` : `Valid p ↔ IsValidPM (Wcl p)` (`Wcl p` the diagonal process matrix).
* `isValidPM_Wcl_pfPoint_iff` : the deterministic valid process matrices are exactly the
  process functions (`PFUL.Countable.IsProcessFunction`).
* `isPure_iff_unitaryLink` : `IsPure V ↔ UnitaryLink (choiMat V)` for every `V`.
* `isValidPM_choiMat_Vsb`, `isPurePM_choiMat_Vsb` : the Switchboard's `W = |Vsb⟩⟩⟨⟨Vsb|` is
  a valid and a pure process matrix in the AFNB sense (all finite ancillas, all CPTP maps).
* `inducedP_eq_born` : the induced classical process is the Born rule of `W`.
* `purification_conjecture_false_choi` : Theorem H.12.1 stated with framework definitions only.
-/
import PFUL.ProcessMatrix
import PFUL.CounterexampleValidity
import PFUL.ChoiLink

set_option linter.unusedSectionVars false

open Finset Matrix PFUL.PM
open scoped ComplexOrder

namespace PFUL.Counterexample

/-- Binary wires. -/
abbrev BW : Fin 3 → Type := fun _ => Bool

/-- The wire assignment `(i_k, o_k)` of the strings `i`, `o`. -/
def wires (i o : Fin 8) : Fin 3 → Bool × Bool := fun k => (bit k i, bit k o)

theorem choiVec_wires {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) (π : P) (φ : F) (e o : Fin 8) :
    choiVec V (π, φ, wires e o) = V (e, φ) (o, π) := choiVec_apply V π φ e o

def wiresEquiv : Fin 8 × Fin 8 ≃ (Fin 3 → Bool × Bool) where
  toFun x := wires x.1 x.2
  invFun a := (bitsEquiv.symm (fun k => (a k).1), bitsEquiv.symm (fun k => (a k).2))
  left_inv x := Prod.ext (bitsEquiv.symm_apply_apply x.1) (bitsEquiv.symm_apply_apply x.2)
  right_inv a := by
    funext k
    exact Prod.ext (congrFun (bitsEquiv.apply_symm_apply (fun k => (a k).1)) k)
      (congrFun (bitsEquiv.apply_symm_apply (fun k => (a k).2)) k)

theorem sum_wires (f : (Fin 3 → Bool × Bool) → ℂ) :
    ∑ a, f a = ∑ i : Fin 8, ∑ o : Fin 8, f (wires i o) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv wiresEquiv (fun x => f (wires x.1 x.2)) f fun _ => rfl).symm

/-! ## The classical process matrix -/

/-- The (diagonal) process matrix `W_p = Σ_{i,o} p(i|o) |i,o⟩⟨i,o|` of a classical process,
with trivial source and sink. -/
noncomputable def Wcl (p : Fin 8 → Fin 8 → ℝ) :
    Matrix (PIdx Unit Unit BW BW) (PIdx Unit Unit BW BW) ℂ :=
  fun x x' => if x.2.2 = x'.2.2 then
    ((p (wiresEquiv.symm x.2.2).1 (wiresEquiv.symm x.2.2).2 : ℝ) : ℂ) else 0

theorem Wcl_wires (p : Fin 8 → Fin 8 → ℝ) (u v : Unit) (i o : Fin 8) (a' : Fin 3 → Bool × Bool) :
    Wcl p (u, v, wires i o) (u, v, a') = if wires i o = a' then (p i o : ℂ) else 0 := by
  have : wiresEquiv.symm (wires i o) = (i, o) := wiresEquiv.symm_apply_apply (i, o)
  simp only [Wcl, this]

/-- Validity with complex-valued local "interventions" with constant row sums: the
multilinear extension of `Valid`. -/
theorem valid_sum_complex {p : Fin 8 → Fin 8 → ℝ} (hp : Valid p) (q : Fin 3 → Bool → Bool → ℂ)
    (c : Fin 3 → ℂ) (hq : ∀ k x, q k x false + q k x true = c k) :
    ∑ i : Fin 8, ∑ o : Fin 8, (p i o : ℂ) * ∏ k, q k (bit k i) (bit k o) = ∏ k, c k := by
  let Dm : Fin 3 → Bool × Bool := ![(false, false), (true, true), (false, true)]
  let lam : Fin 3 → Fin 3 → ℂ := fun k => ![q k true false, q k false true,
    q k false false - q k true false]
  have hdec : ∀ k x y, q k x y = ∑ j : Fin 3, lam k j * if loc (Dm j) x = y then 1 else 0 := by
    intro k x y
    have h0 := hq k false
    have h1 := hq k true
    rw [Fin.sum_univ_three]
    cases x <;> cases y <;> simp [lam, Dm, loc] <;> linear_combination h1 - h0
  have hlam : ∀ k, ∑ j : Fin 3, lam k j = c k := by
    intro k; rw [Fin.sum_univ_three, ← hq k false]; simp [lam]; ring
  have hdet : ∀ g : Fin 3 → Fin 3, ∑ i : Fin 8, ∑ o : Fin 8,
      (p i o : ℂ) * ∏ k, (if loc (Dm (g k)) (bit k i) = bit k o then (1 : ℂ) else 0) = 1 := by
    intro g
    have h := hp.2 (fun k x y => if loc (Dm (g k)) x = y then 1 else 0)
      (fun k x y => by split_ifs <;> norm_num)
      (fun k x => by cases loc (Dm (g k)) x <;> simp)
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_one] at h'
    refine Eq.trans ?_ h'
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hexp : ∀ i o : Fin 8, (p i o : ℂ) * ∏ k, q k (bit k i) (bit k o) =
      ∑ g : Fin 3 → Fin 3, (∏ k, lam k (g k)) *
        ((p i o : ℂ) * ∏ k, (if loc (Dm (g k)) (bit k i) = bit k o then (1 : ℂ) else 0)) := by
    intro i o
    simp_rw [hdec, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum,
      Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hdet, mul_one]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_congr rfl fun k _ => hlam k

/-- The trace condition of the link of `W_p` with arbitrary local Choi matrices. -/
theorem trace_link_Wcl (p : Fin 8 → Fin 8 → ℝ) {X Y : Fin 3 → Type} [∀ k, Fintype (Y k)]
    (C : ∀ k, Matrix ((Bool × X k) × (Bool × Y k)) ((Bool × X k) × (Bool × Y k)) ℂ)
    (π π' : Unit) (ξ ξ' : ∀ k, X k) :
    ∑ b : Unit × (∀ k, Y k), link (Wcl p) C ((π, ξ), b) ((π', ξ'), b) =
      ∑ i : Fin 8, ∑ o : Fin 8, (p i o : ℂ) *
        ∏ k, ∑ y : Y k, C k ((bit k i, ξ k), (bit k o, y)) ((bit k i, ξ' k), (bit k o, y)) := by
  simp only [link, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_comm]
  rw [sum_wires]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun o _ => ?_
  have hW : ∀ a' : Fin 3 → Bool × Bool, Wcl p (π, default, wires i o) (π', default, a') =
      if wires i o = a' then (p i o : ℂ) else 0 := fun a' => by
    rw [Subsingleton.elim π default, Subsingleton.elim π' default]; exact Wcl_wires p _ _ i o a'
  simp only [hW, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

theorem Wcl_posSemidef {p : Fin 8 → Fin 8 → ℝ} (hp : ∀ i o, 0 ≤ p i o) : (Wcl p).PosSemidef := by
  have : Wcl p = Matrix.diagonal fun x =>
      ((p (wiresEquiv.symm x.2.2).1 (wiresEquiv.symm x.2.2).2 : ℝ) : ℂ) := by
    ext x x'
    simp only [Wcl, Matrix.diagonal_apply]
    have hx : x.2.2 = x'.2.2 ↔ x = x' := by
      constructor
      · intro h; exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) h)
      · intro h; rw [h]
    simp only [hx]
  rw [this]
  exact PosSemidef.diagonal fun x => Complex.zero_le_real.2 (hp _ _)

/-- **Validity agrees with AFNB validity of the diagonal process matrix.** -/
theorem isValidPM_Wcl_iff (p : Fin 8 → Fin 8 → ℝ) : IsValidPM (Wcl p) ↔ Valid p := by
  constructor
  · rintro ⟨hW, hC⟩
    refine ⟨fun i o => ?_, fun q hq0 hq1 => ?_⟩
    · have h := hW.diag_nonneg (i := ((), (), wires i o))
      rw [Wcl_wires, if_pos rfl] at h
      exact Complex.zero_le_real.1 h
    · let C : ∀ k, Matrix ((Bool × Unit) × (Bool × Unit)) ((Bool × Unit) × (Bool × Unit)) ℂ :=
        fun k => Matrix.diagonal fun z => ((q k z.1.1 z.2.1 : ℝ) : ℂ)
      have hCk : ∀ k, IsCPTPChoi (C k) := by
        intro k
        refine ⟨PosSemidef.diagonal fun z => Complex.zero_le_real.2 (hq0 _ _ _), fun a a' => ?_⟩
        simp only [C, Matrix.diagonal_apply, Prod.mk.injEq, and_true]
        by_cases h : a = a'
        · subst h
          simp only [ite_true, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton,
            Fintype.sum_bool]
          rw [← Complex.ofReal_add, add_comm, hq1]; simp
        · simp [h]
      obtain ⟨-, htp⟩ := hC (fun _ => Unit) (fun _ => Unit) C hCk
      have h := htp ((), fun _ => ()) ((), fun _ => ())
      rw [if_pos rfl, trace_link_Wcl] at h
      simp only [C, Matrix.diagonal_apply, ite_true, Finset.univ_unique, Finset.sum_singleton] at h
      have h' : ((∑ i : Fin 8, ∑ o : Fin 8, p i o * ∏ k, q k (bit k i) (bit k o) : ℝ) : ℂ) = 1 := by
        rw [← h]; push_cast; rfl
      exact_mod_cast h'
  · intro hp
    refine ⟨Wcl_posSemidef hp.1, fun X Y _ _ _ _ C hC =>
      ⟨link_posSemidef (Wcl_posSemidef hp.1) (fun k => (hC k).1), fun a a' => ?_⟩⟩
    obtain ⟨π, ξ⟩ := a
    obtain ⟨π', ξ'⟩ := a'
    rw [trace_link_Wcl]
    refine (valid_sum_complex hp
      (fun k x y => ∑ yy : Y k, C k ((x, ξ k), (y, yy)) ((x, ξ' k), (y, yy)))
      (fun k => if ξ k = ξ' k then 1 else 0) fun k x => ?_).trans ?_
    · have h := (hC k).2 (x, ξ k) (x, ξ' k)
      rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
      rw [add_comm, h]
      simp
    · rw [Finset.prod_boole]
      simp only [Finset.mem_univ, true_implies, Prod.mk.injEq]
      have : (∀ k, ξ k = ξ' k) ↔ ξ = ξ' := funext_iff.symm
      simp only [true_and]
      exact if_congr this rfl rfl

/-! ## The Switchboard's process matrix -/

theorem Vsb_apply (e o2 u o s t : Fin 8) :
    Vsb (e, (o2, u)) (o, (s, t)) = if o = o2 then (if e = u ^^^ t then board o e s else 0) else 0 := by
  simp only [Vsb]
  rw [← ite_and]
  exact if_congr (by rw [xor_eq_iff' u e t]; exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩)
    rfl rfl

theorem sum_Vsb (f : Fin 8 → Fin 8 → ℂ) (o2 u s t : Fin 8) :
    ∑ e : Fin 8, ∑ o : Fin 8, Vsb (e, (o2, u)) (o, (s, t)) * f e o =
      board o2 (u ^^^ t) s * f (u ^^^ t) o2 := by
  simp only [Vsb_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_star_Vsb (f : Fin 8 → Fin 8 → ℂ) (o2 u s t : Fin 8) :
    ∑ e : Fin 8, ∑ o : Fin 8, star (Vsb (e, (o2, u)) (o, (s, t))) * f e o =
      star (board o2 (u ^^^ t) s) * f (u ^^^ t) o2 := by
  simp only [Vsb_apply, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

set_option maxHeartbeats 1000000 in
/-- **Trace preservation of the Switchboard's link product**: for any local maps that are
trace preserving (`Tr_out C_k = 1`), on any finite ancillas, the link of `|Vsb⟩⟩⟨⟨Vsb|` is
trace preserving. The proof is `scalar_key`, the same multilinear identity as purity. -/
theorem trace_link_Vsb {X Y : Fin 3 → Type} [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)]
    (C : ∀ k, Matrix ((Bool × X k) × (Bool × Y k)) ((Bool × X k) × (Bool × Y k)) ℂ)
    (hC : ∀ k a a', ∑ b, C k (a, b) (a', b) = if a = a' then 1 else 0)
    (π π' : Fin 8 × Fin 8) (ξ ξ' : ∀ k, X k) :
    ∑ b : (Fin 8 × Fin 8) × (∀ k, Y k), link (choiMat Vsb) C ((π, ξ), b) ((π', ξ'), b) =
      if π = π' ∧ ξ = ξ' then 1 else 0 := by
  obtain ⟨s, t⟩ := π
  obtain ⟨s', t'⟩ := π'
  set T : Fin 3 → Bool × Bool → Bool × Bool → ℂ := fun k a a' =>
    ∑ y : Y k, C k ((a.1, ξ k), (a.2, y)) ((a'.1, ξ' k), (a'.2, y)) with hT
  have step1 : ∀ φ : Fin 8 × Fin 8, ∑ η : (∀ k, Y k),
      link (choiMat Vsb) C (((s, t), ξ), (φ, η)) (((s', t'), ξ'), (φ, η)) =
      ∑ e : Fin 8, ∑ o : Fin 8, Vsb (e, φ) (o, (s, t)) * ∑ e' : Fin 8, ∑ o' : Fin 8,
        star (Vsb (e', φ) (o', (s', t'))) * ∏ k, T k (bit k e, bit k o) (bit k e', bit k o') := by
    intro φ
    simp only [link, choiMat, vecMulVec_apply, Pi.star_apply]
    rw [Finset.sum_comm, sum_wires]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm, sum_wires, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o' _ => ?_
    simp only [choiVec_wires, hT]
    simp only [wires]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [step1]
  simp_rw [sum_star_Vsb, sum_Vsb]
  rw [Fintype.sum_prod_type]
  simp only
  set B : Fin 3 → Bool → Bool → Bool → ℂ := fun k x y z => T k (z, x) (y, x) with hB
  have hb : ∀ k y z, B k false y z + B k true y z =
      if y = z then (if ξ k = ξ' k then 1 else 0) else 0 := by
    intro k y z
    have h := hC k (z, ξ k) (y, ξ' k)
    rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
    simp only [hB, hT]
    rw [add_comm, h]
    simp only [Prod.mk.injEq]
    by_cases h1 : y = z
    · subst h1; simp
    · simp [h1, Ne.symm h1]
  have hsh : ∀ o' : Fin 8, ∑ u : Fin 8, board o' (u ^^^ t) s * (star (board o' (u ^^^ t') s') *
      ∏ k, T k (bit k (u ^^^ t), bit k o') (bit k (u ^^^ t'), bit k o')) =
      ∑ e : Fin 8, star (board o' e s') * board o' (e ^^^ (t' ^^^ t)) s *
        ∏ k, B k (bit k o') (bit k e) (bit k (e ^^^ (t' ^^^ t))) := by
    intro o'
    have : ∀ u : Fin 8, board o' (u ^^^ t) s * (star (board o' (u ^^^ t') s') *
        ∏ k, T k (bit k (u ^^^ t), bit k o') (bit k (u ^^^ t'), bit k o')) =
        star (board o' (u ^^^ t') s') * board o' ((u ^^^ t') ^^^ (t' ^^^ t)) s *
        ∏ k, B k (bit k o') (bit k (u ^^^ t')) (bit k ((u ^^^ t') ^^^ (t' ^^^ t))) := by
      intro u; rw [← xor_shift u t' t]; simp only [hB]; ring
    rw [Finset.sum_congr rfl fun u _ => this u]
    exact Fintype.sum_equiv (Function.Involutive.toPerm (fun u => u ^^^ t')
      (fun u => xor_xor_cancel' u t')) _ _ (fun u => rfl)
  simp_rw [hsh]
  rw [scalar_key B _ hb s' s (t' ^^^ t)]
  simp only [xor_eq_zero_iff', Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, Prod.mk.injEq]
  have hα : (∀ k, ξ k = ξ' k) ↔ ξ = ξ' := funext_iff.symm
  by_cases h1 : s = s' <;> by_cases h2 : t = t' <;> by_cases h3 : ξ = ξ' <;>
    simp [h1, h2, h3, hα, eq_comm]

theorem posSemidef_choiMat {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) :
    (choiMat V).PosSemidef := posSemidef_vecMulVec _

/-- **The Switchboard's process matrix is valid in the AFNB sense** (all finite ancillas, all
CPTP local operations). -/
theorem isValidPM_choiMat_Vsb : IsValidPM (I := BW) (O := BW) (choiMat Vsb) :=
  ⟨posSemidef_choiMat _, fun _ _ _ _ _ _ C hC =>
    ⟨link_posSemidef (posSemidef_choiMat _) (fun k => (hC k).1), fun a a' => by
      obtain ⟨π, ξ⟩ := a
      obtain ⟨π', ξ'⟩ := a'
      rw [trace_link_Vsb C (fun k => (hC k).2) π π' ξ ξ']
      simp only [Prod.mk.injEq]⟩⟩

/-- The link of `|V⟩⟩⟨⟨V|` with local pure operations `|A_k⟩⟩⟨⟨A_k|` is `|compose V A⟩⟩⟨⟨…|`. -/
theorem link_choiMat_vecOp {P F : Type} [Fintype P] [Fintype F] [DecidableEq P] [DecidableEq F] (V : Proc P F)
    {X : Fin 3 → Type} (A : ∀ k, Matrix (Bool × X k) (Bool × X k) ℂ) :
    link (I := BW) (O := BW) (choiMat V) (fun k => vecOp (A k)) = vecOp (compose V A) := by
  have h1 : link (I := BW) (O := BW) (choiMat V) (fun k => vecOp (A k)) =
      vecMulVec (linkVec (I := BW) (O := BW) (choiVec V) (fun k => vecOf (A k)))
        (star (linkVec (I := BW) (O := BW) (choiVec V) (fun k => vecOf (A k)))) :=
    link_rankOne _ _
  have h2 : linkVec (I := BW) (O := BW) (choiVec V) (fun k => vecOf (A k)) = vecOf (compose V A) := by
    funext x
    simp only [linkVec, vecOf]
    rw [compose_eq_link, sum_wires, Finset.sum_comm]
    rfl
  rw [h1, h2]; rfl

theorem isUnitaryM_iff_mem {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    IsUnitaryM A ↔ A ∈ Matrix.unitaryGroup n ℂ := by
  exact Iff.rfl

/-- **Purity agrees with AFNB purity** (unitary link) of the Choi projector, for every `V`. -/
theorem isPure_iff_unitaryLink {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) :
    IsPure V ↔ UnitaryLink (I := BW) (O := BW) (choiMat V) := by
  constructor
  · intro h X _ _ A hA
    exact ⟨compose V A, (isUnitaryM_iff_mem _).2 (h X A fun k => (isUnitaryM_iff_mem _).1 (hA k)),
      link_choiMat_vecOp V A⟩
  · intro h X _ _ A hA
    obtain ⟨M, hM, hl⟩ := h X A fun k => (isUnitaryM_iff_mem _).2 (hA k)
    rw [link_choiMat_vecOp] at hl
    exact (isUnitaryM_iff_mem _).1 (isUnitaryM_of_vecOp_eq hM hl)

/-- **The Switchboard is a pure process in the AFNB sense.** -/
theorem isPurePM_choiMat_Vsb : IsPurePM (I := BW) (O := BW) (choiMat Vsb) :=
  ⟨isValidPM_choiMat_Vsb, (isPure_iff_unitaryLink Vsb).1 isPure_Vsb⟩

/-- **Born rule**: the induced classical process is `p(i|o) = Tr[W (ψψ† ⊗ 1_F ⊗ |i,o⟩⟨i,o|)]`. -/
theorem inducedP_eq_born {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) (ψ : P → ℂ)
    (i o : Fin 8) :
    (inducedP V ψ i o : ℂ) = ∑ φ : F, ∑ π : P, ∑ π' : P,
      choiMat V (π, φ, wires i o) (π', φ, wires i o) * ψ π * star (ψ π') := by
  simp only [inducedP, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun π' _ => ?_
  simp only [choiMat, vecMulVec_apply, Pi.star_apply, choiVec_wires, map_mul,
    Complex.star_def]
  ring

/-! ## Process functions and the main theorem in framework terms -/

/-- The deterministic valid diagonal process matrices are exactly the process functions of the
general framework (`PFUL.Countable.IsProcessFunction`). -/
theorem isValidPM_Wcl_pfPoint_iff (w : Fin 8 → Fin 8) :
    IsValidPM (Wcl (pfPoint w)) ↔ PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) := by
  rw [isValidPM_Wcl_iff, valid_pfPoint_iff, isPF_iff]

/-- `p ↦ W_p` as an `ℝ`-linear map. -/
noncomputable def WclL : (Fin 8 → Fin 8 → ℝ) →ₗ[ℝ]
    Matrix (PIdx Unit Unit BW BW) (PIdx Unit Unit BW BW) ℂ where
  toFun := Wcl
  map_add' p q := by
    funext x x'; simp only [Wcl, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c p := by
    funext x x'; simp only [Wcl, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.real_smul]

theorem Wcl_injective : Function.Injective Wcl := by
  intro p q h
  funext i o
  have := congrFun (congrFun h ((), (), wires i o)) ((), (), wires i o)
  rw [Wcl_wires, Wcl_wires] at this
  simpa using this

theorem Wcl_mem_convexHull_iff (p : Fin 8 → Fin 8 → ℝ) (S : Set (Fin 8 → Fin 8 → ℝ)) :
    Wcl p ∈ convexHull ℝ (Wcl '' S) ↔ p ∈ convexHull ℝ S := by
  have h : Wcl '' S = WclL '' S := rfl
  rw [h, ← LinearMap.image_convexHull]
  exact ⟨fun ⟨x, hx, hxp⟩ => (Wcl_injective hxp) ▸ hx, fun hp => ⟨p, hp, rfl⟩⟩

/-- **Theorem H.12.1 in the process-matrix framework.** There is a classical process whose
diagonal process matrix `W_p` is valid (AFNB: positive, and every link with CPTP local maps on
any finite ancillas is a CPTP map), which is the Born-rule marginal of a process matrix
`W = |V⟩⟩⟨⟨V|` that is pure in the AFNB sense (valid, and the link with unitaries on any
finite ancillas is a unitary), with a normalised source state, but which is not a convex
combination of the valid deterministic process matrices (the process functions). -/
theorem purification_conjecture_false_choi :
    ∃ p : Fin 8 → Fin 8 → ℝ, IsValidPM (Wcl p) ∧
      (∃ (P F : Type) (_ : Fintype P) (_ : Fintype F) (_ : DecidableEq P) (_ : DecidableEq F)
        (W : Matrix (PIdx P F BW BW) (PIdx P F BW BW) ℂ) (ψ : P → ℂ),
        IsPurePM W ∧ (∑ π, ‖ψ π‖ ^ 2) = 1 ∧
        ∀ i o, (p i o : ℂ) = ∑ φ : F, ∑ π : P, ∑ π' : P,
          W (π, φ, wires i o) (π', φ, wires i o) * ψ π * star (ψ π')) ∧
      Wcl p ∉ convexHull ℝ {W | ∃ w : Fin 8 → Fin 8, W = Wcl (pfPoint w) ∧ IsValidPM W} := by
  refine ⟨pcl, (isValidPM_Wcl_iff _).2 valid_pcl,
    ⟨Fin 8 × Fin 8, Fin 8 × Fin 8, inferInstance, inferInstance, inferInstance, inferInstance,
      choiMat Vsb, psiSrc, isPurePM_choiMat_Vsb, norm_psiSrc, fun i o => ?_⟩, ?_⟩
  · rw [inducedP_Vsb]; exact inducedP_eq_born Vsb psiSrc i o
  · have hS : {W | ∃ w : Fin 8 → Fin 8, W = Wcl (pfPoint w) ∧ IsValidPM W} = Wcl '' PFset := by
      ext W
      constructor
      · rintro ⟨w, rfl, hv⟩
        exact ⟨pfPoint w, ⟨w, (valid_pfPoint_iff w).1 ((isValidPM_Wcl_iff _).1 hv), rfl⟩, rfl⟩
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, rfl, (isValidPM_Wcl_iff _).2 ((valid_pfPoint_iff w).2 hw)⟩
    rw [hS, Wcl_mem_convexHull_iff]
    exact pcl_not_mem_convexHull

end PFUL.Counterexample

#print axioms PFUL.Counterexample.isValidPM_Wcl_iff
#print axioms PFUL.Counterexample.trace_link_Vsb
#print axioms PFUL.Counterexample.isValidPM_choiMat_Vsb
#print axioms PFUL.Counterexample.isPure_iff_unitaryLink
#print axioms PFUL.Counterexample.isPurePM_choiMat_Vsb
#print axioms PFUL.Counterexample.inducedP_eq_born
#print axioms PFUL.Counterexample.isValidPM_Wcl_pfPoint_iff
#print axioms PFUL.Counterexample.purification_conjecture_false_choi
