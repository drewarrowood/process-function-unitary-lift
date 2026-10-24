/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# The general (finite-dimensional) process-matrix framework

Araújo, Feix, Navascués and Brukner (AFNB 2017, Sec. 2), for an **arbitrary** operator `W`
(the earlier files `PFUL.Validity` / `PFUL.Choi` only treat `W = |U_w⟩⟩⟨⟨U_w|` for a process
function `w`):

* `IsCPTPChoi J` : `J` is the Choi matrix of a CPTP map (PSD, and `Tr_out J = 1_in`);
  `isCPTPChoi_choiOf_iff` ties this to `PFUL.Choi.IsCP` via Choi's theorem `isCP_iff_choi`.
* `link W C` : the link product `G = W ∗ (C_1 ⊗ … ⊗ C_n)` of a process matrix on
  `P ⊗ F ⊗ ⨂_k (I_k ⊗ O_k)` with local Choi matrices on `(I_k ⊗ X_k) ⊗ (O_k ⊗ Y_k)`.
* `link_posSemidef` : the link product of PSD matrices is PSD.
* `link_rankOne` : the link of rank-one (pure) matrices is rank one, `|V⟩⟩ ∗ |A⟩⟩ = |M⟩⟩`.
* `IsValidPM W` : `W ≥ 0` and the link is CPTP for **all** finite ancillas and **all** CPTP
  local operations (AFNB validity).
* `UnitaryLink W` / `IsPurePM W` : AFNB Definition 1, purity: valid, and the link with local
  unitaries is the Choi projector of a unitary.
-/
import PFUL.ChoiThm
import Mathlib.Analysis.InnerProductSpace.Positive

set_option linter.unusedSectionVars false

open Finset Matrix
open scoped ComplexOrder

namespace PFUL.PM

local instance : AddLeftMono ℂ :=
  ⟨fun a b c h => by
    rw [Complex.le_def] at h ⊢
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith [h.1], by rw [h.2]⟩⟩

/-! ## CPTP Choi matrices -/

/-- Choi matrix (index `in × out`) of a CPTP map: positive semidefinite (complete positivity,
by Choi's theorem) and `Σ_b J (a,b) (a',b) = δ_{aa'}` (trace preservation). -/
def IsCPTPChoi {A B : Type} [Fintype B] [DecidableEq A] (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  J.PosSemidef ∧ ∀ a a', ∑ b, J (a, b) (a', b) = if a = a' then 1 else 0

/-- **Choi's theorem, CPTP form**: `choiOf Φ` is a CPTP Choi matrix iff `Φ` is completely
positive (`PFUL.Choi.IsCP`) and trace preserving. -/
theorem isCPTPChoi_choiOf_iff {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    IsCPTPChoi (PFUL.Choi.choiOf Φ) ↔ PFUL.Choi.IsCP Φ ∧ ∀ X, (Φ X).trace = X.trace := by
  have htr : ∀ a a', ∑ b, PFUL.Choi.choiOf Φ (a, b) (a', b) =
      (Φ (Matrix.single a a' 1)).trace := by
    intro a a'; simp [PFUL.Choi.choiOf, Matrix.trace]
  have hts : ∀ a a' : A, (Matrix.single a a' (1 : ℂ)).trace = if a = a' then 1 else 0 := by
    intro a a'
    by_cases h : a = a'
    · subst h; simp [Matrix.trace]
    · simp [Matrix.trace, h]
  rw [IsCPTPChoi, ← PFUL.Choi.isCP_iff_choi]
  refine and_congr Iff.rfl ⟨fun h X => ?_, fun h a a' => ?_⟩
  · conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Matrix.trace_sum]
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    have : Matrix.single a a' (X a a') = X a a' • Matrix.single a a' (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, Matrix.trace_smul, Matrix.trace_smul, ← htr, h, hts]
  · rw [htr, h, hts]

/-! ## The link product -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I O : ι → Type}
  [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
  {P F : Type} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]

/-- Index of a process matrix: source `P`, sink `F`, and each party's wires `(i_k, o_k)`
(the layout of `PFUL.Counterexample.choiMat`). -/
abbrev PIdx (P F : Type) (I O : ι → Type) := P × F × (∀ k, I k × O k)

/-- **Link product** `W ∗ (C_1 ⊗ … ⊗ C_n)` (Chiribella, D'Ariano, Perinotti): contract the
wires `(i_k, o_k)` of `W` with those of the local Choi matrices `C_k`, whose index is
`(i_k, x_k) × (o_k, y_k)` (`X_k`, `Y_k` input and output ancillas). The result is the Choi
matrix (index `in × out` = `(P × X) × (F × Y)`) of the induced map `P ⊗ X → F ⊗ Y`. -/
def link (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) {X Y : ι → Type}
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) :
    Matrix ((P × ∀ k, X k) × (F × ∀ k, Y k)) ((P × ∀ k, X k) × (F × ∀ k, Y k)) ℂ :=
  fun x x' => ∑ a : (∀ k, I k × O k), ∑ a' : (∀ k, I k × O k),
    W (x.1.1, x.2.1, a) (x'.1.1, x'.2.1, a') *
      ∏ k, C k (((a k).1, x.1.2 k), ((a k).2, x.2.2 k)) (((a' k).1, x'.1.2 k), ((a' k).2, x'.2.2 k))

/-- The Choi vector `|A⟩⟩ (c, r) = A r c` of a linear map with matrix `A` (rows = outputs). -/
def vecOf {R C : Type} (A : Matrix R C ℂ) (x : C × R) : ℂ := A x.2 x.1

/-- `|A⟩⟩⟨⟨A|`, the Choi matrix of the map `ρ ↦ A ρ A†`; equal to `PFUL.Choi.choi` of the
single Kraus operator `A` (`vecOp_eq_choi`). -/
def vecOp {R C : Type} (A : Matrix R C ℂ) : Matrix (C × R) (C × R) ℂ :=
  vecMulVec (vecOf A) (star (vecOf A))

theorem vecOp_eq_choi {R C : Type} (A : Matrix R C ℂ) :
    vecOp A = PFUL.Choi.choi (fun _ : Unit => A) := by
  ext x x'; simp [vecOp, vecOf, PFUL.Choi.choi, vecMulVec_apply]

/-- The vector of the link of rank-one operators. -/
def linkVec (v : PIdx P F I O → ℂ) {X Y : ι → Type} (u : ∀ k, (I k × X k) × (O k × Y k) → ℂ)
    (x : (P × ∀ k, X k) × (F × ∀ k, Y k)) : ℂ :=
  ∑ a : (∀ k, I k × O k), v (x.1.1, x.2.1, a) * ∏ k, u k (((a k).1, x.1.2 k), ((a k).2, x.2.2 k))

/-- **Link of pure operators is pure**: `|v⟩⟨v| ∗ ⨂ |u_k⟩⟨u_k| = |v ∗ u⟩⟨v ∗ u|`. -/
theorem link_rankOne (v : PIdx P F I O → ℂ) {X Y : ι → Type}
    (u : ∀ k, (I k × X k) × (O k × Y k) → ℂ) :
    link (vecMulVec v (star v)) (fun k => vecMulVec (u k) (star (u k))) =
      vecMulVec (linkVec v u) (star (linkVec v u)) := by
  ext x x'
  simp only [link, linkVec, vecMulVec_apply, Pi.star_apply, star_sum, star_mul', star_prod,
    Finset.sum_mul_sum, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

theorem link_sum_left {J : Type} [Fintype J] (W : J → Matrix (PIdx P F I O) (PIdx P F I O) ℂ)
    {X Y : ι → Type} (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) :
    link (∑ j, W j : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) C = ∑ j, link (W j) C := by
  ext x x'
  simp only [link, Matrix.sum_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]

theorem link_sum_right (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) {X Y : ι → Type}
    {J : ι → Type} [∀ k, Fintype (J k)]
    (D : ∀ k, J k → Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) :
    link W (fun k => (∑ j, D k j : Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ)) =
      ∑ g : (∀ k, J k), link W (fun k => D k (g k)) := by
  ext x x'
  simp only [link, Matrix.sum_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]

theorem choi_eq_sum {A B J : Type} [Fintype J] (K : J → Matrix B A ℂ) :
    PFUL.Choi.choi K = ∑ j, vecMulVec (vecOf (K j)) (star (vecOf (K j))) := by
  ext x x'; simp [PFUL.Choi.choi, vecOf, Matrix.sum_apply, vecMulVec_apply]

theorem posSemidef_vecMulVec {n : Type} [Fintype n] (v : n → ℂ) :
    (vecMulVec v (star v)).PosSemidef := by
  have : vecMulVec v (star v) = (replicateRow Unit (star v))ᴴ * replicateRow Unit (star v) := by
    ext x y; simp [vecMulVec_apply, Matrix.mul_apply, replicateRow]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

/-- **Positivity of the link product**: PSD process matrix and PSD local Choi matrices give a
PSD Choi matrix. -/
theorem link_posSemidef {W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ} (hW : W.PosSemidef)
    {X Y : ι → Type} [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)] [∀ k, Fintype (Y k)]
    [∀ k, DecidableEq (Y k)]
    {C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ}
    (hC : ∀ k, (C k).PosSemidef) : (link W C).PosSemidef := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hW
  choose K hK _ using fun k => PFUL.Choi.kraus_of_choi (C k) (hC k)
  have hC' : C = fun k => ∑ j, vecMulVec (vecOf (K k j)) (star (vecOf (K k j))) := by
    funext k; rw [← choi_eq_sum, hK k]
  rw [hC', hv, link_sum_left]
  refine posSemidef_sum _ fun i _ => ?_
  rw [link_sum_right]
  refine posSemidef_sum _ fun g _ => ?_
  rw [link_rankOne]
  exact posSemidef_vecMulVec _

/-! ## Validity and purity -/

/-- **AFNB validity** of an arbitrary process matrix: `W ≥ 0`, and for all finite input and
output ancillas and all CPTP local operations, the link product is (the Choi matrix of) a
CPTP map `P ⊗ X → F ⊗ Y`. -/
def IsValidPM (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  W.PosSemidef ∧ ∀ (X Y : ι → Type) [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
    [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ),
    (∀ k, IsCPTPChoi (C k)) → IsCPTPChoi (link W C)

/-- A (rectangular) matrix is unitary: `A† A = 1` and `A A† = 1`. -/
def IsUnitaryM {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C ℂ) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

/-- The link of `W` with local unitaries (on any finite ancillas) is the Choi projector
`|M⟩⟩⟨⟨M|` of a unitary `M : P ⊗ X → F ⊗ X`. -/
def UnitaryLink (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  ∀ (X : ι → Type) [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
    (A : ∀ k, Matrix (O k × X k) (I k × X k) ℂ), (∀ k, IsUnitaryM (A k)) →
    ∃ M : Matrix (F × ∀ k, X k) (P × ∀ k, X k) ℂ, IsUnitaryM M ∧
      link W (fun k => vecOp (A k)) = vecOp M

/-- **AFNB Definition 1 (pure process)**: valid, and unitary under local unitaries. -/
def IsPurePM (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) : Prop :=
  IsValidPM W ∧ UnitaryLink W

/-- A matrix whose Choi projector equals that of a unitary is itself unitary. -/
theorem isUnitaryM_of_vecOp_eq {R C : Type} [Fintype R] [Fintype C] [DecidableEq R]
    [DecidableEq C] {A M : Matrix R C ℂ} (hM : IsUnitaryM M) (h : vecOp A = vecOp M) :
    IsUnitaryM A := by
  have e : ∀ x x', vecOf A x * star (vecOf A x') = vecOf M x * star (vecOf M x') := by
    intro x x'; have := congrFun (congrFun h x) x'; simpa [vecOp, vecMulVec_apply] using this
  refine ⟨?_, ?_⟩
  · ext c c'
    have := congrFun (congrFun hM.1 c) c'
    rw [Matrix.mul_apply] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := e (c', r) (c, r)
    simp only [vecOf] at this
    simp only [conjTranspose_apply]
    rw [mul_comm, this, mul_comm]
  · ext r r'
    have := congrFun (congrFun hM.2 r) r'
    rw [Matrix.mul_apply] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := e (c, r) (c, r')
    simp only [vecOf] at this
    simp only [conjTranspose_apply]
    exact this

end PFUL.PM

#print axioms PFUL.PM.isCPTPChoi_choiOf_iff
#print axioms PFUL.PM.link_posSemidef
#print axioms PFUL.PM.link_rankOne
#print axioms PFUL.PM.isUnitaryM_of_vecOp_eq
