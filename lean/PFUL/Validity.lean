import PFUL.Column
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Appendix A in Lean: unitarity under local unitaries ⇒ valid process (finite dimensions)

Local operations are given by Stinespring dilations: each party `k` applies a unitary
`V k : I k × X k → O k × Y k`, where `X k` holds the party's input-side ancillas (Stinespring ancilla
in a fixed state, shared/entangled ancillas) and `Y k` the output-side ancillas (Stinespring environment,
instrument records, kept ancillas). The joint initial state `σ` of the source and *all* input ancillas is an
arbitrary density matrix, so entanglement between parties and with the source is allowed.
The resulting global state is `M σ Mᴴ`; the sink state is its partial trace over the output ancillas.
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL

local instance : AddLeftMono ℂ :=
  ⟨fun a b c h => by
    rw [Complex.le_def] at h ⊢
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith [h.1], by rw [h.2]⟩⟩

/-- Partial trace over the second factor. -/
def ptrace {A B : Type*} [Fintype B] (ρ : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a a' => ∑ b, ρ (a, b) (a', b)

/-- Embedding `A → A × B` at a fixed second index. -/
def slot {A B : Type*} [DecidableEq A] [DecidableEq B] (b : B) : Matrix (A × B) A ℂ :=
  fun p a => if p = (a, b) then 1 else 0

lemma ptrace_eq_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) : ptrace ρ = ∑ b, (slot b)ᴴ * ρ * slot b := by
  ext a a'
  simp only [ptrace, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, slot]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [ite_mul, mul_ite]

theorem ptrace_posSemidef {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ : Matrix (A × B) (A × B) ℂ} (h : ρ.PosSemidef) : (ptrace ρ).PosSemidef := by
  rw [ptrace_eq_sum]
  exact posSemidef_sum _ (fun b _ => h.conjTranspose_mul_mul_same _)

theorem trace_ptrace {A B : Type*} [Fintype A] [Fintype B] (ρ : Matrix (A × B) (A × B) ℂ) :
    (ptrace ρ).trace = ρ.trace := by
  simp [ptrace, Matrix.trace, Fintype.sum_prod_type]

/-- Density matrix: positive semidefinite with unit trace. -/
def IsDensity {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- A unitary `M` maps density matrices to density matrices, and so does the reduced map after
tracing out the output ancillas. -/
theorem density_of_isometry {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (M : Matrix (A × B) C ℂ) (hM : Mᴴ * M = 1) {σ : Matrix C C ℂ} (hσ : IsDensity σ) :
    IsDensity (M * σ * Mᴴ) ∧ IsDensity (ptrace (M * σ * Mᴴ)) := by
  have hpsd : (M * σ * Mᴴ).PosSemidef := hσ.1.mul_mul_conjTranspose_same M
  have htr : (M * σ * Mᴴ).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hM, Matrix.one_mul, hσ.2]
  exact ⟨⟨hpsd, htr⟩, ⟨ptrace_posSemidef hpsd, by rw [trace_ptrace, htr]⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]

/-- **AFNB validity as used in Appendix A** (for given ancilla types `X`, `Y`): for every choice of
local unitaries (Stinespring dilations of the local operations) and every joint density matrix of
source and input ancillas, the global output, and the sink state obtained by tracing out the output
ancillas, are density matrices. -/
def ValidWith (w : (∀ k, O k) → (∀ k, I k)) (X Y : ι → Type*)
    [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)] [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)] :
    Prop :=
  ∀ (V : ∀ k, Matrix (O k × Y k) (I k × X k) ℂ), (∀ k, V k * (V k)ᴴ = 1) → (∀ k, (V k)ᴴ * V k = 1) →
    ∀ σ : Matrix ((∀ k, I k) × (∀ k, X k)) ((∀ k, I k) × (∀ k, X k)) ℂ, IsDensity σ →
      IsDensity (induced ℂ w V * σ * (induced ℂ w V)ᴴ) ∧
      IsDensity (ptrace (induced ℂ w V * σ * (induced ℂ w V)ᴴ))

/-- **Appendix A, formalised (finite dimensions).** The source-sink lift of every process function is
valid in the AFNB sense, for all finite ancilla types: local operations given by Stinespring
unitaries, arbitrary (entangled) joint states of source and ancillas, sink state by partial trace. -/
theorem valid (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w) (X Y : ι → Type*)
    [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)] [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)] :
    ValidWith w X Y := by
  intro V hV hV' σ hσ
  exact density_of_isometry _ (induced_conjTranspose_mul_of_colnorm w hw V hV hV') hσ

end PFUL

#print axioms PFUL.valid
#print axioms PFUL.density_of_isometry
