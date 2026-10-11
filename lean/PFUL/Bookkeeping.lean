import PFUL.ChoiAnc
import PFUL.ChoiThm
import PFUL.Channels

/-!
# Bookkeeping: group-free ancillas and the split layout of `ValidWith`
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL.Choi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- Choi vector of the lift with identity ancilla wires (no structure on the ancilla types). -/
def liftVecAnc (w : (∀ k, O k) → (∀ k, I k))
    (x : (∀ k, I k × X k) × ((∀ k, O k × Y k) × (∀ k, (I k × X k) × (O k × Y k)))) : ℂ :=
  if x.2.2 = (fun k => ((w (fun k => (x.2.1 k).1) k + (x.1 k).1, (x.1 k).2), x.2.1 k)) then 1 else 0

/-- Generalised Born rule with party ancillas, group-free. -/
def bornAnc (w : (∀ k, O k) → (∀ k, I k)) (ρ : Matrix (∀ k, I k × X k) (∀ k, I k × X k) ℂ)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) : ℂ :=
  ∑ x, ∑ x', liftVecAnc w x * star (liftVecAnc w x') *
    (ρ x.1 x'.1 * ((if x.2.1 = x'.2.1 then 1 else 0) * ∏ k, C k (x.2.2 k) (x'.2.2 k)))

theorem bornAnc_eq_bornC [∀ k, AddCommGroup (X k)] (w : (∀ k, O k) → (∀ k, I k))
    (ρ : Matrix (∀ k, I k × X k) (∀ k, I k × X k) ℂ)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) :
    bornAnc w ρ C = bornC (wAnc (X := X) (Y := Y) w) ρ C := by
  have h : ∀ x, liftVecAnc (X := X) (Y := Y) w x = liftVec (wAnc w) x := by
    intro x
    simp only [liftVecAnc, liftVec, wAnc_apply_add]
  simp only [bornAnc, bornC, procMat, h]

/-- **Group-free AFNB normalisation with party ancillas.** Ancilla types need only be finite. -/
theorem bornAnc_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (ρ : Matrix (∀ k, I k × X k) (∀ k, I k × X k) ℂ) (hρ : ρ.trace = 1)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ)
    (hC : ∀ k, (C k).PosSemidef)
    (htp : ∀ k i i', ∑ o, C k (i', o) (i, o) = if i = i' then 1 else 0) :
    bornAnc w ρ C = 1 := by
  classical
  by_cases hne : ∀ k, Nonempty (X k)
  · letI : ∀ k, AddCommGroup (X k) := fun k =>
      haveI : NeZero (Fintype.card (X k)) := ⟨Fintype.card_ne_zero⟩
      (Fintype.equivFin (X k)).addCommGroup
    rw [bornAnc_eq_bornC]
    exact bornC_anc_eq_one w hw ρ hρ C hC htp
  · exfalso
    push Not at hne
    obtain ⟨k, hk⟩ := hne
    haveI : IsEmpty (∀ k, I k × X k) := ⟨fun c => hk.false (c k).2⟩
    rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at hρ
    exact zero_ne_one hρ

/-- The split layout of `ValidWith` vs the joint layout used in the Choi form. -/
def splitEquiv : ((∀ k, I k) × (∀ k, X k)) ≃ (∀ k, I k × X k) where
  toFun c k := (c.1 k, c.2 k)
  invFun p := (fun k => (p k).1, fun k => (p k).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Born rule for a source state in the split layout of `ValidWith`. -/
def bornSplit (w : (∀ k, O k) → (∀ k, I k))
    (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ) : ℂ :=
  bornAnc w (σ.submatrix splitEquiv.symm splitEquiv.symm) C

lemma trace_submatrix_equiv' {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix n n ℂ) :
    (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact e.sum_comp (fun i => A i i)

/-- **Split-layout AFNB normalisation** (the source state indexed exactly as in `ValidWith`). -/
theorem bornSplit_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ) (hσ : σ.trace = 1)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ)
    (hC : ∀ k, (C k).PosSemidef)
    (htp : ∀ k i i', ∑ o, C k (i', o) (i, o) = if i = i' then 1 else 0) :
    bornSplit w σ C = 1 :=
  bornAnc_eq_one w hw _ (by rw [trace_submatrix_equiv']; exact hσ) C hC htp

/-- **Everything together.** For every process function and all finite ancilla types:
(a) `ValidWith` (local unitaries; global output and sink state are density matrices);
(b) the same for arbitrary local CPTP maps in Kraus form (Stinespring isometries);
(c) AFNB normalisation `Tr[W (σ ⊗ 1 ⊗ ⨂ C_k)ᵀ] = 1` for every source-and-ancilla state `σ` in the
split layout and all local Choi matrices that are CP (`isCP_iff_choi`) and TP. -/
theorem validity_package (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w) :
    ValidWith w X Y ∧
    (∀ {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
      (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ), (∀ k, ∑ j, (K k j)ᴴ * K k j = 1) →
      ∀ σ, IsDensity σ →
        IsDensity (induced ℂ w (fun k => krausDilP (K k)) * σ * (induced ℂ w (fun k => krausDilP (K k)))ᴴ) ∧
        IsDensity (ptrace (induced ℂ w (fun k => krausDilP (K k)) * σ *
          (induced ℂ w (fun k => krausDilP (K k)))ᴴ))) ∧
    (∀ (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ), σ.trace = 1 →
      ∀ C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ,
      (∀ k, (C k).PosSemidef) → (∀ k i i', ∑ o, C k (i', o) (i, o) = if i = i' then 1 else 0) →
      bornSplit w σ C = 1) :=
  ⟨valid w hw X Y, fun K hK σ hσ => valid_kraus w hw K hK σ hσ,
    fun σ hσ C hC htp => bornSplit_eq_one w hw σ hσ C hC htp⟩

/-- Induced source(+ancillas, split layout) → sink(+ancillas) ⊗ Kraus-record map, group-free. -/
def indSplit {J : ι → Type*} (w : (∀ k, O k) → (∀ k, I k))
    (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ) :
    Matrix ((∀ k, O k × Y k) × (∀ k, J k)) ((∀ k, I k) × (∀ k, X k)) ℂ :=
  fun r c => ∏ k, K k (r.2 k) (r.1 k) (w (fun k => (r.1 k).1) k + c.1 k, c.2 k)

theorem bornSplit_eq_trace {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hX : ∀ k, Nonempty (X k))
    (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ)
    (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ) :
    bornSplit w σ (fun k => choi (K k)) = (indSplit w K * σ * (indSplit w K)ᴴ).trace := by
  classical
  letI : ∀ k, AddCommGroup (X k) := fun k =>
    haveI : NeZero (Fintype.card (X k)) := ⟨Fintype.card_ne_zero⟩
    (Fintype.equivFin (X k)).addCommGroup
  have hM : indM (wAnc (X := X) (Y := Y) w) K = (indSplit w K).submatrix id splitEquiv.symm := by
    ext r c
    simp only [indM, indSplit, submatrix_apply, id, wAnc_apply_add]
    rfl
  rw [bornSplit, bornAnc_eq_bornC]
  show born (wAnc w) _ K = _
  rw [born_eq_trace, hM]
  have : (indSplit w K).submatrix id splitEquiv.symm * σ.submatrix splitEquiv.symm splitEquiv.symm *
      ((indSplit w K).submatrix id splitEquiv.symm)ᴴ = indSplit w K * σ * (indSplit w K)ᴴ := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  rw [this]

/-- **Split-layout equivalence** of AFNB normalisation and density-matrix validity, for fixed local
Kraus channels with ancillas (group-free, any map `w`). -/
theorem afnb_iff_density_split {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (w : (∀ k, O k) → (∀ k, I k)) (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ) :
    (∀ σ, IsDensity σ → bornSplit w σ (fun k => choi (K k)) = 1) ↔
      (∀ σ, IsDensity σ → IsDensity (indSplit w K * σ * (indSplit w K)ᴴ)) := by
  classical
  by_cases hX : ∀ k, Nonempty (X k)
  · constructor
    · intro h σ hσ
      exact ⟨hσ.1.mul_mul_conjTranspose_same _, by rw [← bornSplit_eq_trace w hX]; exact h σ hσ⟩
    · intro h σ hσ
      rw [bornSplit_eq_trace w hX]; exact (h σ hσ).2
  · push Not at hX
    obtain ⟨k, hk⟩ := hX
    have hempty : ∀ σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ,
        ¬ IsDensity σ := by
      intro σ hσ
      haveI : IsEmpty ((∀ k, I k) × (∀ k, X k)) := ⟨fun c => hk.false (c.2 k)⟩
      have := hσ.2
      rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at this
      exact zero_ne_one this
    exact ⟨fun _ σ hσ => absurd hσ (hempty σ), fun _ σ hσ => absurd hσ (hempty σ)⟩

end PFUL.Choi

#print axioms PFUL.Choi.bornAnc_eq_one
#print axioms PFUL.Choi.bornSplit_eq_one
#print axioms PFUL.Choi.validity_package
#print axioms PFUL.Choi.afnb_iff_density_split
