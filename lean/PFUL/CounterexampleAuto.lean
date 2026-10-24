/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 11: automatic boundedness and ancillas of any cardinality (Switchboard)

Rounds 9-10 stated the Switchboard's unitarity for *bounded* local unitaries on `ℓ²(Bool × κ_k)`
with *countable* ancilla types `κ_k`. Neither hypothesis is needed:

* `unitary_of_unitaryKernel` (automatic boundedness): a kernel with orthonormal columns and
  orthonormal rows, over an index set of any cardinality, is the matrix of a bounded unitary
  (a surjective linear isometry) of `ℓ²`. No operator, continuity or boundedness is assumed.
* `isUnitaryKer_Vsb`: for every family of ancilla types (any cardinality) and every family of
  local *unitary kernels* (orthonormal rows and columns, no boundedness assumed), the closed
  loop's kernel `compose Vsb a` is the matrix of a bounded unitary of `ℓ²(P × ∏ κ_k)`.
* `isUnitaryAll_Vsb`: the Round 10 statement `IsUnitaryInf` with the `Countable` hypothesis
  removed; `ℓ²(κ)` for arbitrary `κ` is every Hilbert space up to unitary equivalence
  (Hilbert bases), so this covers non-separable ancillas.
-/
import PFUL.CounterexampleUnitary

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

namespace PFUL.Counterexample

/-- **Automatic boundedness.** A unitary kernel (orthonormal columns and rows) on an index set
of any cardinality is the matrix of a bounded unitary of `ℓ²`. -/
theorem unitary_of_unitaryKernel {X : Type} [DecidableEq X] (M : Matrix X X ℂ)
    (hc : IsIsoKernel M) (hr : IsCoIsoKernel M) :
    ∃ U : L2 X ≃ₗᵢ[ℂ] L2 X, ∀ r c, U (lp.single 2 c (1 : ℂ)) r = M r c := by
  obtain ⟨U, hU⟩ := exists_isometry_of_isIsoKernel M hc
  have he : (fun r c => U (lp.single 2 c (1 : ℂ)) r) = M := by funext r c; exact hU r c
  have hrow : IsCoIsoKernel (fun r c => U (lp.single 2 c (1 : ℂ)) r) := by rw [he]; exact hr
  exact ⟨LinearIsometryEquiv.ofSurjective U (surjective_of_isCoIsoKernel U hrow), hU⟩

/-- Kernel-level unitarity against ancillas of any cardinality, with local operations given
only as unitary kernels (no boundedness hypothesis). -/
def IsUnitaryKer {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, DecidableEq (κ k)] (a : ∀ k, Matrix (Bool × κ k) (Bool × κ k) ℂ),
    (∀ k, IsIsoKernel (a k)) → (∀ k, IsCoIsoKernel (a k)) →
      ∃ U : L2 (P × (∀ k, κ k)) ≃ₗᵢ[ℂ] L2 (P × (∀ k, κ k)),
        ∀ r c, U (lp.single 2 c (1 : ℂ)) r = compose V a r c

/-- **The Switchboard loop is unitary for all unitary kernels and all ancillas.** -/
theorem isUnitaryKer_Vsb : IsUnitaryKer Vsb := by
  intro κ _ a hc hr
  exact unitary_of_unitaryKernel _ (isPureKer_Vsb κ a hc) (isCoIsoKernel_compose_Vsb a hr)

/-- Unitary purity against bounded local unitaries on ancillas of **any** cardinality
(`IsUnitaryInf` without `Countable`). -/
def IsUnitaryAll {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, DecidableEq (κ k)]
    (A : ∀ k, L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k)),
    (∀ k, A k ∈ unitary (L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k))) →
      ∃ U : L2 (P × (∀ k, κ k)) ≃ₗᵢ[ℂ] L2 (P × (∀ k, κ k)),
        ∀ r c, U (lp.single 2 c (1 : ℂ)) r = composeOp V A r c

theorem IsUnitaryKer.isUnitaryAll {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsUnitaryKer V) : IsUnitaryAll V := by
  intro κ _ A hA
  exact h κ (fun k => entOp (A k)) (fun k => isIsoKernel_entOp (A k) (hA k))
    (fun k => isCoIsoKernel_entOp (A k) (hA k))

theorem IsUnitaryAll.isUnitaryInf {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsUnitaryAll V) : IsUnitaryInf V := by
  intro κ _ _ A hA
  exact h κ A hA

/-- **The Switchboard is unitary against ancillas of any cardinality.** -/
theorem isUnitaryAll_Vsb : IsUnitaryAll Vsb := isUnitaryKer_Vsb.isUnitaryAll

/-- Purifiability by a process that is unitary for all unitary kernels on all ancillas. -/
def PurifiableUnitaryKer (p : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∃ (V : Proc (Fin 8 × Fin 8) (Fin 8 × Fin 8)) (ψ : Fin 8 × Fin 8 → ℂ),
    (∑ π, ‖ψ π‖ ^ 2) = 1 ∧ IsUnitaryKer V ∧ IsUnitaryAll V ∧ IsPure V ∧ p = inducedP V ψ

/-- **Theorem H.12.1, strongest form**: valid, purifiable by a loop that is unitary against
all ancillas (any cardinality) and all local unitary kernels (no boundedness assumed), and
outside the process-function hull. -/
theorem purification_conjecture_false_unitaryKer :
    ∃ p : Fin 8 → Fin 8 → ℝ, Valid p ∧ PurifiableUnitaryKer p ∧
      p ∉ convexHull ℝ {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
        (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} := by
  have hset : {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} = PFset := by
    ext x; simp only [PFset, Set.mem_ofPred_eq, isPF_iff]
  have h3 := pcl_not_mem_convexHull
  rw [← hset] at h3
  exact ⟨pcl, valid_pcl, ⟨Vsb, psiSrc, norm_psiSrc, isUnitaryKer_Vsb, isUnitaryAll_Vsb,
    isPure_Vsb, inducedP_Vsb⟩, h3⟩

end PFUL.Counterexample
