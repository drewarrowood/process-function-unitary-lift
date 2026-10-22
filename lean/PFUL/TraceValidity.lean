import PFUL.Assemble
import PFUL.TraceClass

/-!
# Countable alphabets: validity as a statement about trace-class density operators

The countable-alphabet unitary layer (`PFUL.Countable.induced_unitary_l2`) gives a unitary
`Φ : ℓ²(sources × input ancillas) ≃ ℓ²(sink outputs × output ancillas)`. With the trace class
`PFUL.TraceClass.traceClass`, the trace and the partial trace `PFUL.TraceClass.ptraceR` on
`ℓ²(I × J)`, validity is restated in the Born-rule form used in finite dimensions
(`PFUL.density_of_isometry`): for every input density operator `ρ` (positive, trace class, unit trace;
entangled ancillas allowed) the global output `Φ ρ Φ†` and the reduced sink state
`Tr_Y (Φ ρ Φ†)` are density operators, in particular `Tr = 1`.
-/

open ContinuousLinearMap PFUL.TraceClass

universe u v

namespace PFUL.Countable

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type u}

/-- **Validity on countable alphabets, trace form.** Same hypotheses as `induced_unitary_l2`. The
induced unitary `Φ` sends every density operator `ρ` on `ℓ²(sources × input ancillas)` to a density
operator, and tracing out the output ancillas `Y` leaves a density operator on `ℓ²(sink outputs)`:
`Tr [Tr_Y (Φ ρ Φ†)] = 1`. -/
theorem valid_density_l2 {X Y : ι → Type u} [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)]
    [∀ k, Countable (X k)] [∀ k, Countable (O k)] [∀ k, Countable (Y k)]
    [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (hcol : ∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 ≃ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      (∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) ∧
      ∀ ρ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
          lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2, IsDensity ρ →
        let U : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
            lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2 := Φ
        IsDensity (U ∘L ρ ∘L adjoint U) ∧ IsDensity (ptraceR (U ∘L ρ ∘L adjoint U)) ∧
          trace (ptraceR (U ∘L ρ ∘L adjoint U)) = 1 := by
  obtain ⟨Φ, -, h2⟩ := induced_unitary_l2 w hw V hsq hrow hcol
  refine ⟨Φ, h2, fun ρ hρ => ?_⟩
  have h := hρ.conj _ (adjoint_comp_self_linearIsometryEquiv Φ)
  exact ⟨h, h.ptraceR, h.ptraceR.2.2⟩

end PFUL.Countable

#print axioms PFUL.Countable.valid_density_l2
