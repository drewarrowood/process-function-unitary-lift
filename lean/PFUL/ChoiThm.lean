import PFUL.Choi

/-!
# Choi's theorem (finite dimensions)

A linear map `Φ : Matrix I I ℂ → Matrix O O ℂ` is completely positive (every ampliation
`Φ ⊗ id_n` preserves positive semidefiniteness) iff its Choi matrix is positive semidefinite.
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL.Choi

local instance : AddLeftMono ℂ :=
  ⟨fun a b c h => by
    rw [Complex.le_def] at h ⊢
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith [h.1], by rw [h.2]⟩⟩

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- `Φ ⊗ id_R` acting on `Matrix (I × R) (I × R)`. -/
def ampliate (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (R : Type*) (Xm : Matrix (I × R) (I × R) ℂ) :
    Matrix (O × R) (O × R) ℂ :=
  fun p p' => Φ (Matrix.of fun i i' => Xm (i, p.2) (i', p'.2)) p.1 p'.1

/-- Complete positivity: `Φ ⊗ id_n` preserves positive semidefiniteness for every `n`. -/
def IsCP (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ (n : ℕ) (Xm : Matrix (I × Fin n) (I × Fin n) ℂ), Xm.PosSemidef → (ampliate Φ (Fin n) Xm).PosSemidef

/-- Choi matrix `C (i,o) (i',o') = Φ(|i⟩⟨i'|) o o'`. -/
def choiOf (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix (I × O) (I × O) ℂ :=
  fun p p' => Φ (Matrix.single p.1 p'.1 1) p.2 p'.2

theorem cp_choi_posSemidef (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : IsCP Φ) :
    (choiOf Φ).PosSemidef := by
  classical
  set e := Fintype.equivFin I
  let v : I × Fin (Fintype.card I) → ℂ := fun p => if e p.1 = p.2 then 1 else 0
  have hX := h _ (vecMulVec v (star v)) (posSemidef_vecMulVec_self_star v)
  have hsub := hX.submatrix (fun p : I × O => (p.2, e p.1))
  convert hsub using 1
  ext p p'
  simp only [choiOf, ampliate, submatrix_apply]
  have hm : (Matrix.of fun i i' => vecMulVec v (star v) (i, e p.1) (i', e p'.1)) =
      Matrix.single p.1 p'.1 (1 : ℂ) := by
    ext i i'
    simp only [Matrix.of_apply, vecMulVec_apply, v, Pi.star_apply, Matrix.single_apply,
      e.injective.eq_iff]
    by_cases h1 : i = p.1 <;> by_cases h2 : i' = p'.1 <;> simp [h1, h2, eq_comm]
  rw [hm]

theorem apply_eq_sum_choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (Xm : Matrix I I ℂ) (o o' : O) :
    Φ Xm o o' = ∑ i, ∑ i', Xm i i' * choiOf Φ (i, o) (i', o') := by
  conv_lhs => rw [matrix_eq_sum_single Xm]
  have hs : ∀ i i', Matrix.single i i' (Xm i i') = Xm i i' • Matrix.single i i' (1 : ℂ) := by
    intro i i'; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [hs, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choiOf]

theorem choi_posSemidef_cp (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : (choiOf Φ).PosSemidef) :
    IsCP Φ := by
  classical
  obtain ⟨K, hK, -⟩ := kraus_of_choi _ h
  intro n Xm hXm
  let A : (I × O) → Matrix (O × Fin n) (I × Fin n) ℂ := fun j =>
    Matrix.of fun p q => K j p.1 q.1 * (if p.2 = q.2 then 1 else 0)
  have hA : ampliate Φ (Fin n) Xm = ∑ j, A j * Xm * (A j)ᴴ := by
    ext p p'
    rw [ampliate, apply_eq_sum_choi, ← hK]
    simp only [choi, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, A,
      Fintype.sum_prod_type, star_mul', mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul,
      apply_ite star, star_one, star_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i'; rw [Finset.sum_comm]; arg 2; ext j1; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]; arg 2; ext j1; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
      Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))))
    ring
  rw [hA]
  exact posSemidef_sum _ (fun j _ => hXm.mul_mul_conjTranspose_same _)

/-- **Choi's theorem.** -/
theorem isCP_iff_choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : IsCP Φ ↔ (choiOf Φ).PosSemidef :=
  ⟨cp_choi_posSemidef Φ, choi_posSemidef_cp Φ⟩

end PFUL.Choi
#print axioms PFUL.Choi.isCP_iff_choi
