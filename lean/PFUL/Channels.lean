import PFUL.Isometry
import PFUL.Validity

/-!
# Kraus channels, Stinespring dilations, instruments (finite dimensions)
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL

local instance : AddLeftMono ℂ :=
  ⟨fun a b c h => by
    rw [Complex.le_def] at h ⊢
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith [h.1], by rw [h.2]⟩⟩

/-- Stinespring dilation of a Kraus family: `V = ∑ j, K j ⊗ |j⟩`, the Kraus index going to the
output environment. -/
def krausDil {R C J : Type*} (K : J → Matrix R C ℂ) : Matrix (R × J) C ℂ :=
  fun p c => K p.2 p.1 c

theorem krausDil_isometry {R C J : Type*} [Fintype R] [Fintype J] [DecidableEq C]
    (K : J → Matrix R C ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) : (krausDil K)ᴴ * krausDil K = 1 := by
  rw [← hK]
  ext c c'
  simp only [Matrix.mul_apply, conjTranspose_apply, krausDil, Matrix.sum_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The dilation reproduces the channel: tracing out the Kraus index of `V ρ Vᴴ` gives
`∑ j, K j ρ (K j)ᴴ`. -/
theorem ptrace_krausDil {R C J : Type*} [Fintype C] [Fintype J]
    (K : J → Matrix R C ℂ) (ρ : Matrix C C ℂ) :
    ptrace (krausDil K * ρ * (krausDil K)ᴴ) = ∑ j, K j * ρ * (K j)ᴴ := by
  ext r r'
  simp [ptrace, Matrix.mul_apply, conjTranspose_apply, krausDil, Matrix.sum_apply]

/-- Outcome-conditioned (sub-normalised) states: keep the part of the output-ancilla sum with
outcome label `g b = z`. -/
def outcomeState {A B Z : Type*} [Fintype B] [DecidableEq Z] (g : B → Z)
    (ρ : Matrix (A × B) (A × B) ℂ) (z : Z) : Matrix A A ℂ :=
  fun a a' => ∑ b ∈ Finset.univ.filter (fun b => g b = z), ρ (a, b) (a', b)

theorem outcomeState_posSemidef {A B Z : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [DecidableEq Z] (g : B → Z) {ρ : Matrix (A × B) (A × B) ℂ}
    (h : ρ.PosSemidef) (z : Z) : (outcomeState g ρ z).PosSemidef := by
  have : outcomeState g ρ z = ∑ b ∈ Finset.univ.filter (fun b => g b = z), (slot b)ᴴ * ρ * slot b := by
    ext a a'
    simp only [outcomeState, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, slot]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [ite_mul, mul_ite]
  rw [this]
  exact posSemidef_sum _ (fun b _ => h.conjTranspose_mul_mul_same _)

theorem sum_outcomeState {A B Z : Type*} [Fintype B] [Fintype Z] [DecidableEq Z] (g : B → Z)
    (ρ : Matrix (A × B) (A × B) ℂ) : ∑ z, outcomeState g ρ z = ptrace ρ := by
  ext a a'
  simp only [Matrix.sum_apply, outcomeState, ptrace]
  exact Finset.sum_fiberwise _ g _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- Party-shaped Stinespring dilation: output `O × (Y × J)`. -/
def krausDilP {O' Y' C J : Type*} (K : J → Matrix (O' × Y') C ℂ) : Matrix (O' × (Y' × J)) C ℂ :=
  fun p c => K p.2.2 (p.1, p.2.1) c

theorem krausDilP_isometry {O' Y' C J : Type*} [Fintype O'] [Fintype Y'] [Fintype J] [DecidableEq C]
    (K : J → Matrix (O' × Y') C ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) : (krausDilP K)ᴴ * krausDilP K = 1 := by
  rw [← hK]
  ext c c'
  simp only [Matrix.mul_apply, conjTranspose_apply, krausDilP, Matrix.sum_apply, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext o; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- **Gap 1: validity for arbitrary local channels in Kraus form.** Each party applies a CPTP map
`I k × X k → O k × Y k` with Kraus operators `K k j` (`∑ j, (K k j)ᴴ K k j = 1`), realised by its
Stinespring isometry `krausDilP (K k)` (Kraus index appended to the output ancillas). For any joint
density matrix `σ` of source and input ancillas, the global output and the sink state are density
matrices. -/
theorem valid_kraus (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ) (hK : ∀ k, ∑ j, (K k j)ᴴ * K k j = 1)
    (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ) (hσ : IsDensity σ) :
    IsDensity (induced ℂ w (fun k => krausDilP (K k)) * σ * (induced ℂ w (fun k => krausDilP (K k)))ᴴ) ∧
    IsDensity (ptrace (induced ℂ w (fun k => krausDilP (K k)) * σ *
      (induced ℂ w (fun k => krausDilP (K k)))ᴴ)) :=
  density_of_isometry _ (induced_isometry w hw _ (fun k => krausDilP_isometry (K k) (hK k))) hσ

/-- **Gap 2: instruments.** Each party applies an instrument: Kraus operators `K k a j` indexed by
outcome `a ∈ A k` and Kraus index `j`, with `∑ (a,j), Kᴴ K = 1`. With the outcome recorded in the
output ancilla, every outcome-conditioned sink state `ρ_a` (for a joint outcome `a : ∀ k, A k`) is
positive semidefinite, and `∑ a, ρ_a` is a density matrix; so outcome probabilities `tr ρ_a`
are nonnegative and sum to one. -/
theorem valid_instrument (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    {A : ι → Type*} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (K : ∀ k, A k × J k → Matrix (O k × Y k) (I k × X k) ℂ)
    (hK : ∀ k, ∑ j, (K k j)ᴴ * K k j = 1)
    (σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ) (hσ : IsDensity σ) :
    let ρ := induced ℂ w (fun k => krausDilP (K k)) * σ * (induced ℂ w (fun k => krausDilP (K k)))ᴴ
    let g : (∀ k, Y k × (A k × J k)) → (∀ k, A k) := fun y k => (y k).2.1
    (∀ a, (outcomeState g ρ a).PosSemidef) ∧ IsDensity (∑ a, outcomeState g ρ a) ∧
    ∑ a, (outcomeState g ρ a).trace = 1 := by
  intro ρ g
  have h := valid_kraus w hw K hK σ hσ
  refine ⟨fun a => outcomeState_posSemidef g h.1.1 a, ?_, ?_⟩
  · rw [sum_outcomeState]; exact h.2
  · rw [← Matrix.trace_sum, sum_outcomeState]; exact h.2.2

end PFUL

#print axioms PFUL.valid_kraus
#print axioms PFUL.valid_instrument
#print axioms PFUL.ptrace_krausDil
