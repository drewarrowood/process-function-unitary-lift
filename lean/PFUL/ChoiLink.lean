/-
Link between the counterexample's process formalism (`Proc`, `compose`, `IsPure`) and the
Choi / process-matrix form `W = |V⟩⟩⟨⟨V|` used in `PFUL.Choi`.

* `choiVec V` : the Choi vector of a process `V : O ⊗ P → I ⊗ F`, indexed like `PFUL.Choi.Idx`
  (past, future, per-party wires).
* `choiMat V = |V⟩⟩⟨⟨V|` and its rank-one / Hermitian / idempotent-up-to-trace structure.
* `compose_eq_link` : `compose V A` is the link product of the Choi vector with the local
  operations, i.e. it only depends on `V` through `choiVec V`.
* `choiMat_Vsb` : the Switchboard's process matrix is the rank-one `|Vsb⟩⟩⟨⟨Vsb|`, and
  `Vsb_pure_choi` packages purity together with this form.
-/
import PFUL.CounterexampleLink

set_option linter.unusedSectionVars false

open Finset Matrix

namespace PFUL.Counterexample

variable {P F : Type} [Fintype P] [Fintype F]

/-- Choi vector of a process: amplitude at past `π`, future `φ`, and wires `(i_k, o_k)` is the
matrix element `⟨i, φ| V |o, π⟩`. -/
def choiVec (V : Proc P F) (x : P × F × (Fin 3 → Bool × Bool)) : ℂ :=
  V (bitsEquiv.symm (fun k => (x.2.2 k).1), x.2.1) (bitsEquiv.symm (fun k => (x.2.2 k).2), x.1)

/-- Process matrix `W = |V⟩⟩⟨⟨V|`. -/
def choiMat (V : Proc P F) :
    Matrix (P × F × (Fin 3 → Bool × Bool)) (P × F × (Fin 3 → Bool × Bool)) ℂ :=
  vecMulVec (choiVec V) (star (choiVec V))

theorem choiVec_apply (V : Proc P F) (π : P) (φ : F) (e o : Fin 8) :
    choiVec V (π, φ, fun k => (bit k e, bit k o)) = V (e, φ) (o, π) := by
  simp only [choiVec]
  congr 2 <;> exact bitsEquiv.symm_apply_eq.2 (funext fun k => rfl)

/-- `compose` is the link product of the Choi vector with the local operations. -/
theorem compose_eq_link (V : Proc P F) {a : Fin 3 → Type} (A : ∀ k, Matrix (Bool × a k) (Bool × a k) ℂ)
    (φβ : F × (∀ k, a k)) (πα : P × (∀ k, a k)) :
    compose V A φβ πα = ∑ o : Fin 8, ∑ e : Fin 8,
      choiVec V (πα.1, φβ.1, fun k => (bit k e, bit k o)) *
        ∏ k, A k (bit k o, φβ.2 k) (bit k e, πα.2 k) := by
  simp only [compose, choiVec_apply]

/-- Two processes with the same Choi vector have the same compositions (so purity is a
property of `|V⟩⟩`). -/
theorem compose_congr_choiVec {V V' : Proc P F} (h : choiVec V = choiVec V')
    {a : Fin 3 → Type} (A : ∀ k, Matrix (Bool × a k) (Bool × a k) ℂ) :
    compose V A = compose V' A := by
  funext φβ πα; rw [compose_eq_link, compose_eq_link, h]

theorem choiMat_isHermitian (V : Proc P F) : (choiMat V).IsHermitian := by
  ext x y; simp [choiMat, vecMulVec_apply, mul_comm]

/-- `W² = (tr W) W`: the process matrix is rank one, `W = |V⟩⟩⟨⟨V|`. -/
theorem choiMat_sq (V : Proc P F) : choiMat V * choiMat V = (choiMat V).trace • choiMat V := by
  ext x y
  simp only [choiMat, mul_apply, vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.smul_apply,
    smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- The Switchboard (the process realising the H.12 counterexample) is pure, and its process
matrix is the rank-one `W = |Vsb⟩⟩⟨⟨Vsb|` with `W² = (tr W) W`. -/
theorem Vsb_pure_choi :
    IsPure Vsb ∧ choiMat Vsb = vecMulVec (choiVec Vsb) (star (choiVec Vsb)) ∧
      choiMat Vsb * choiMat Vsb = (choiMat Vsb).trace • choiMat Vsb ∧ (choiMat Vsb).IsHermitian :=
  ⟨isPure_Vsb, rfl, choiMat_sq _, choiMat_isHermitian _⟩

end PFUL.Counterexample
