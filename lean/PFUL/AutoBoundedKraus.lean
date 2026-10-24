import PFUL.AutoBounded
import PFUL.KrausAny

/-!
# Round 16 corollaries: the normality hypothesis is redundant

With `PFUL.TraceClass.IsCPTP.isNormalCPTP` (PFUL/AutoBounded.lean), every statement proved for
normal CPTP maps holds for all CPTP maps on the trace class.
-/

open PFUL.TraceClass PFUL.Countable

universe u

/-- **Kraus ⟺ CPTP on `ℓ²` of any cardinality** (no boundedness assumption). -/
theorem isCPTP_iff_kraus_any {O A : Type u} [DecidableEq O]
    [DecidableEq A] {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
      (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} :
    IsCPTP Φ ↔ ∃ (Y : Type u) (_ : DecidableEq Y) (V : O × Y → A → ℂ)
      (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)),
      ∀ ρ ∈ traceClass (lp (fun _ : A => ℂ) 2), Φ ρ = krausChannel V hiso ρ :=
  isNormalCPTP_iff.symm.trans isNormalCPTP_iff_kraus_any

namespace PFUL.Counterexample

/-- **Validity of the Switchboard against arbitrary CPTP local channels** on ancillas of any
cardinality: `valid_normalCPTP_Vsb_any` without the normality hypothesis. -/
theorem valid_CPTP_Vsb_any {X X' : Fin 3 → Type} [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (X' k)]
    (Φ : ∀ k, (lp (fun _ : Bool × X k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X k => ℂ) 2) →
      (lp (fun _ : Bool × X' k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X' k => ℂ) 2))
    (hΦ : ∀ k, IsCPTP (Φ k)) :
    ∃ (Y : Fin 3 → Type) (_ : ∀ k, DecidableEq (Y k))
      (V : ∀ k, (Bool × X' k) × Y k → Bool × X k → ℂ)
      (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)),
      (∀ k, ∀ ρ ∈ traceClass (lp (fun _ : Bool × X k => ℂ) 2),
        Φ k ρ = krausChannel (V k) (hiso k) ρ) ∧
      IsNormalCPTP (krausChannel (krausLoop V) (isIsoKernel_krausLoop V hiso)) :=
  valid_normalCPTP_Vsb_any Φ fun k => (hΦ k).isNormalCPTP

end PFUL.Counterexample
