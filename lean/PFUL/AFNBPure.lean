/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13, gap (c): AFNB Theorem 2 in the process-matrix framework

Araújo, Feix, Navascués, Brukner, *A purification postulate for quantum mechanics with
indefinite causal order*, Quantum 1, 10 (2017), arXiv:1611.08535, Theorem 2: a process is pure
iff its process matrix is the Choi projector `|U⟩⟩⟨⟨U|` of a unitary `U : P ⊗ O → F ⊗ I`.

Our `UnitaryLink` uses the same ancilla `X_k` on the input and output side of party `k`, so we
assume `σ k : I k ≃ O k` (equal local input and output dimensions; AFNB allow different ancilla
dimensions, which removes this restriction there).

* `exists_unitary_of_unitaryLink` (forward): `UnitaryLink W → ∃ U, IsUnitaryM U ∧ W = choiPM U`
  (AFNB's proof: close every slot with a SWAP between the wire and a copy of it in the ancilla).
* `unitaryLink_choiPM` (converse): if `|P| = |F|` and `choiPM U` is valid, then its link with
  local unitaries is `|M⟩⟩⟨⟨M|` with `M` unitary (rank-one links are rank one; trace preservation
  gives `M† M = 1`; squareness gives `M M† = 1`).
* `isPurePM_iff` : `IsPurePM W ↔ IsValidPM W ∧ ∃ U, IsUnitaryM U ∧ W = choiPM U`.
-/
import PFUL.ProcessMatrix

open Matrix Finset

set_option linter.unusedSectionVars false

namespace PFUL.PM

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I O : ι → Type}
  [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
  {P F : Type} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]

/-- The vector `|U⟩⟩` of a matrix `U : P ⊗ O → F ⊗ I`, in the process-matrix index layout. -/
def pvec (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) (x : PIdx P F I O) : ℂ :=
  U (x.2.1, fun k => (x.2.2 k).1) (x.1, fun k => (x.2.2 k).2)

/-- The process matrix `|U⟩⟩⟨⟨U|`. -/
def choiPM (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) : Matrix (PIdx P F I O) (PIdx P F I O) ℂ :=
  vecMulVec (pvec U) (star (pvec U))

/-- The local SWAP `I k × I k → O k × I k`, `(i, x) ↦ (σ x, i)`. -/
def swapM (σ : ∀ k, I k ≃ O k) (k : ι) : Matrix (O k × I k) (I k × I k) ℂ :=
  fun r c => if r = (σ k c.2, c.1) then 1 else 0

theorem vecOf_swapM (σ : ∀ k, I k ≃ O k) (k : ι) (a : I k × O k) (ξ η : I k) :
    vecOf (swapM σ k) ((a.1, ξ), (a.2, η)) = if a = (η, σ k ξ) then 1 else 0 := by
  simp only [vecOf, swapM, Prod.mk.injEq]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h2.symm h1
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem star_boole (p : Prop) [Decidable p] : star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem isUnitaryM_swapM (σ : ∀ k, I k ≃ O k) (k : ι) : IsUnitaryM (swapM σ k) := by
  let e : I k × I k ≃ O k × I k :=
    { toFun := fun c => (σ k c.2, c.1)
      invFun := fun r => (r.2, (σ k).symm r.1)
      left_inv := fun c => by simp
      right_inv := fun r => by simp }
  have hs : ∀ r c, swapM σ k r c = if r = e c then 1 else 0 := fun _ _ => rfl
  have hs' : ∀ r c, swapM σ k r c = if e.symm r = c then 1 else 0 := by
    intro r c; rw [hs]; exact if_congr (by rw [e.symm_apply_eq]) rfl rfl
  constructor
  · ext c c'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [conjTranspose_apply, hs, star_boole, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    exact if_congr e.injective.eq_iff rfl rfl
  · ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [conjTranspose_apply, hs', star_boole, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    exact if_congr (by rw [eq_comm, e.symm.injective.eq_iff]) rfl rfl

/-- The link of `W` with local SWAPs is `W` itself, relabelled. -/
theorem link_swap (σ : ∀ k, I k ≃ O k) (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ)
    (x x' : (P × ∀ k, I k) × (F × ∀ k, I k)) :
    link W (fun k => vecOp (swapM σ k)) x x' =
      W (x.1.1, x.2.1, fun k => (x.2.2 k, σ k (x.1.2 k)))
        (x'.1.1, x'.2.1, fun k => (x'.2.2 k, σ k (x'.1.2 k))) := by
  simp only [link, vecOp, vecMulVec_apply, Pi.star_apply]
  have hp : ∀ (a a' : ∀ k, I k × O k), (∏ k, vecOf (swapM σ k) (((a k).1, x.1.2 k), ((a k).2, x.2.2 k)) *
      star (vecOf (swapM σ k) (((a' k).1, x'.1.2 k), ((a' k).2, x'.2.2 k)))) =
      (if a = (fun k => (x.2.2 k, σ k (x.1.2 k))) then 1 else 0) *
        (if a' = (fun k => (x'.2.2 k, σ k (x'.1.2 k))) then 1 else 0) := by
    intro a a'
    simp only [vecOf_swapM, star_boole, Finset.prod_mul_distrib,
      Finset.prod_boole, Finset.mem_univ, forall_true_left, funext_iff]
  simp only [hp, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

/-- **AFNB Theorem 2, forward direction.** -/
theorem exists_unitary_of_unitaryLink (σ : ∀ k, I k ≃ O k)
    {W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ} (hW : UnitaryLink W) :
    ∃ U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ, IsUnitaryM U ∧ W = choiPM U := by
  obtain ⟨M, hM, hl⟩ := hW I (swapM σ) (isUnitaryM_swapM σ)
  let τ : (P × ∀ k, O k) ≃ (P × ∀ k, I k) :=
    Equiv.prodCongr (Equiv.refl P) (Equiv.piCongrRight fun k => (σ k).symm)
  refine ⟨M.submatrix id τ, ⟨?_, ?_⟩, ?_⟩
  · ext c c'
    have := congrFun (congrFun hM.1 (τ c)) (τ c')
    simp only [Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id, Matrix.one_apply,
      τ.injective.eq_iff] at this ⊢
    exact this
  · ext r r'
    have := congrFun (congrFun hM.2 r) r'
    simp only [Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id] at this ⊢
    rw [← this]
    exact Equiv.sum_comp τ (fun c => M r c * star (M r' c))
  · ext ⟨π, φ, a⟩ ⟨π', φ', a'⟩
    have h := congrFun (congrFun hl ((π, fun k => (σ k).symm (a k).2), (φ, fun k => (a k).1)))
      ((π', fun k => (σ k).symm (a' k).2), (φ', fun k => (a' k).1))
    rw [link_swap] at h
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    simp [choiPM, pvec, vecOp, vecMulVec_apply, vecOf, τ]
    rfl

theorem isCPTPChoi_vecOp {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    {A : Matrix R C ℂ} (hA : Aᴴ * A = 1) : IsCPTPChoi (vecOp A) := by
  refine ⟨posSemidef_vecMulVec _, fun c c' => ?_⟩
  have := congrFun (congrFun hA c') c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [conjTranspose_apply] at this
  simp only [vecOp, vecMulVec_apply, Pi.star_apply, vecOf]
  rw [show (∑ b, A b c * star (A b c')) = ∑ b, star (A b c') * A b c from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
  exact if_congr eq_comm rfl rfl

/-- **AFNB Theorem 2, converse direction** (for `|P| = |F|`). -/
theorem unitaryLink_choiPM (hPF : Fintype.card P = Fintype.card F)
    (U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ) (hV : IsValidPM (choiPM U)) :
    UnitaryLink (choiPM U) := by
  intro X _ _ A hA
  let w := linkVec (pvec U) (fun k => vecOf (A k))
  let M : Matrix (F × ∀ k, X k) (P × ∀ k, X k) ℂ := fun r c => w (c, r)
  have hl : link (choiPM U) (fun k => vecOp (A k)) = vecOp M := by
    simp only [choiPM, vecOp]
    rw [link_rankOne]
    rfl
  have hC := hV.2 X X (fun k => vecOp (A k)) fun k => isCPTPChoi_vecOp (hA k).1
  rw [hl] at hC
  have h1 : Mᴴ * M = 1 := by
    ext c c'
    have := hC.2 c' c
    simp only [vecOp, vecMulVec_apply, Pi.star_apply, vecOf] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [conjTranspose_apply]
    rw [show (∑ r, star (M r c) * M r c') = ∑ r, M r c' * star (M r c) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
    by_cases h : c = c' <;> simp [h, eq_comm]
  refine ⟨M, ⟨h1, ?_⟩, hl⟩
  have e : (P × ∀ k, X k) ≃ (F × ∀ k, X k) :=
    Equiv.prodCongr (Fintype.equivOfCardEq hPF) (Equiv.refl _)
  exact (mul_eq_one_comm_of_equiv e).1 h1

/-- **AFNB Theorem 2** (equal local input/output dimensions, `|P| = |F|`): a process matrix is
pure iff it is valid and equal to `|U⟩⟩⟨⟨U|` for a unitary `U : P ⊗ O → F ⊗ I`. -/
theorem isPurePM_iff (σ : ∀ k, I k ≃ O k) (hPF : Fintype.card P = Fintype.card F)
    (W : Matrix (PIdx P F I O) (PIdx P F I O) ℂ) :
    IsPurePM W ↔ IsValidPM W ∧ ∃ U : Matrix (F × ∀ k, I k) (P × ∀ k, O k) ℂ,
      IsUnitaryM U ∧ W = choiPM U := by
  constructor
  · rintro ⟨hv, hu⟩
    exact ⟨hv, exists_unitary_of_unitaryLink σ hu⟩
  · rintro ⟨hv, U, -, rfl⟩
    exact ⟨hv, unitaryLink_choiPM hPF U hv⟩

end PFUL.PM
