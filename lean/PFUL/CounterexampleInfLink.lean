/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13: the counterexample with the infinite-ancilla link product

`purification_conjecture_false_choiInf` restates `purification_conjecture_false_choi` with the
validity and purity predicates of `PFUL.InfiniteLink`, in which the local operations are CPTP
Choi kernels (validity) or unitary kernels (purity) on ancilla types of any cardinality.
-/
import PFUL.InfiniteLink
import PFUL.CounterexampleChoi

open Finset Matrix PFUL.PM
open scoped ComplexOrder

namespace PFUL.Counterexample

/-- Classical validity is AFNB validity against CPTP kernels on arbitrary ancillas. -/
theorem isValidPMInf_Wcl_iff (p : Fin 8 → Fin 8 → ℝ) : IsValidPMInf (Wcl p) ↔ Valid p :=
  (isValidPMInf_iff _).trans (isValidPM_Wcl_iff p)

/-- The Switchboard process matrix is pure against unitary kernels on arbitrary ancillas. -/
theorem isPurePMInf_choiMat_Vsb : IsPurePMInf (I := BW) (O := BW) (choiMat Vsb) :=
  (isPurePMInf_iff (fun _ => Equiv.refl Bool) _).2 isPurePM_choiMat_Vsb

/-- **Theorem H.12.1 with the infinite-ancilla link product.** -/
theorem purification_conjecture_false_choiInf :
    ∃ p : Fin 8 → Fin 8 → ℝ, IsValidPMInf (Wcl p) ∧
      (∃ (P F : Type) (_ : Fintype P) (_ : Fintype F) (_ : DecidableEq P) (_ : DecidableEq F)
        (W : Matrix (PIdx P F BW BW) (PIdx P F BW BW) ℂ) (ψ : P → ℂ),
        IsPurePMInf W ∧ (∑ π, ‖ψ π‖ ^ 2) = 1 ∧
        ∀ i o, (p i o : ℂ) = ∑ φ : F, ∑ π : P, ∑ π' : P,
          W (π, φ, wires i o) (π', φ, wires i o) * ψ π * star (ψ π')) ∧
      Wcl p ∉ convexHull ℝ {W | ∃ w : Fin 8 → Fin 8, W = Wcl (pfPoint w) ∧ IsValidPMInf W} := by
  obtain ⟨p, hv, ⟨P, F, i1, i2, i3, i4, W, ψ, hW, hψ, hp⟩, hh⟩ := purification_conjecture_false_choi
  refine ⟨p, (isValidPMInf_iff _).2 hv,
    ⟨P, F, i1, i2, i3, i4, W, ψ, (isPurePMInf_iff (fun _ => Equiv.refl Bool) _).2 hW, hψ, hp⟩, ?_⟩
  have hS : {W | ∃ w : Fin 8 → Fin 8, W = Wcl (pfPoint w) ∧ IsValidPMInf W} =
      {W | ∃ w : Fin 8 → Fin 8, W = Wcl (pfPoint w) ∧ IsValidPM W} := by
    ext W; simp only [Set.mem_ofPred_eq, isValidPMInf_iff]
  rw [hS]; exact hh

end PFUL.Counterexample
