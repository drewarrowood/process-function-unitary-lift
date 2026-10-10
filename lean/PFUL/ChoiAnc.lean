import PFUL.Choi
import PFUL.Validity

/-!
# Choi form with party ancillas, the converse, and Choi's theorem
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL.Choi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, AddCommGroup (X k)] [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
variable [∀ k, Fintype (Y k)] [∀ k, DecidableEq (Y k)]

/-- The lift with ancilla wires: party `k` receives `(w f k + e k, x k)` from the source `(e, x)` and
its output `(f k, y k)` goes to the sink. Ancilla wires are identity channels. -/
def wAnc (w : (∀ k, O k) → (∀ k, I k)) : (∀ k, O k × Y k) → (∀ k, I k × X k) :=
  fun f k => (w (fun k => (f k).1) k, 0)

theorem wAnc_apply_add (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, O k × Y k) (c : ∀ k, I k × X k)
    (k : ι) : (wAnc (X := X) w f k + c k) = (w (fun k => (f k).1) k + (c k).1, (c k).2) := by
  simp [wAnc, Prod.ext_iff]

theorem wAnc_isProcessFunction (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w) :
    IsProcessFunction (wAnc (X := X) (Y := Y) w) := by
  intro g
  obtain ⟨s, hs, hu⟩ := hw (fun k i => (g k (i, 0)).1)
  refine ⟨fun k => (s k, (g k (w s k, 0)).2), fun k => ?_, fun t ht => ?_⟩
  · simp only [wAnc]
    exact Prod.ext (by simpa using hs k) rfl
  · have h1 : (fun k => (t k).1) = s := hu _ (fun k => by
      have := congrArg Prod.fst (ht k); simpa [wAnc] using this)
    funext k
    have := ht k
    simp only [wAnc] at this
    rw [← this, h1]
    exact Prod.ext (by simpa using hs k) rfl

/-- **Gap (1): AFNB normalisation with party ancillas.** Local CPTP maps
`I k × X k → O k × Y k` (Kraus form), source state `ρ` of the source together with *all* input
ancillas (so shared or entangled ancillas are folded into it), sink = `F × Y`. -/
theorem born_anc_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    {J : ι → Type*} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (ρ : Matrix (∀ k, I k × X k) (∀ k, I k × X k) ℂ) (hρ : ρ.trace = 1)
    (K : ∀ k, J k → Matrix (O k × Y k) (I k × X k) ℂ) (hK : ∀ k, ∑ j, (K k j)ᴴ * K k j = 1) :
    born (wAnc (X := X) (Y := Y) w) ρ K = 1 :=
  born_eq_one _ (wAnc_isProcessFunction w hw) ρ hρ K hK

/-- The same with Choi matrices (CP = PSD Choi matrix, TP = identity partial trace). -/
theorem bornC_anc_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (ρ : Matrix (∀ k, I k × X k) (∀ k, I k × X k) ℂ) (hρ : ρ.trace = 1)
    (C : ∀ k, Matrix ((I k × X k) × (O k × Y k)) ((I k × X k) × (O k × Y k)) ℂ)
    (hC : ∀ k, (C k).PosSemidef)
    (htp : ∀ k i i', ∑ o, C k (i', o) (i, o) = if i = i' then 1 else 0) :
    bornC (wAnc (X := X) (Y := Y) w) ρ C = 1 :=
  bornC_eq_one _ (wAnc_isProcessFunction w hw) ρ hρ C hC htp

/-- The process matrix of the lift is positive semidefinite (`W = |U⟩⟩⟨⟨U|`). -/
theorem procMat_posSemidef {I' O' : ι → Type*} [∀ k, AddCommGroup (I' k)] [∀ k, Fintype (I' k)]
    [∀ k, DecidableEq (I' k)] [∀ k, Fintype (O' k)] [∀ k, DecidableEq (O' k)]
    (w : (∀ k, O' k) → (∀ k, I' k)) : (procMat w).PosSemidef := by
  have := posSemidef_vecMulVec_self_star (liftVec w)
  convert this using 1
  ext x x'
  simp [procMat, vecMulVec_apply]

/-- **Gap (2): equivalence of the two validity conditions** (for any map `w`, process function or
not, and any fixed local CPTP maps in Kraus form): AFNB normalisation of the Born rule for all source
states is equivalent to the density-matrix condition that the induced output `M ρ Mᴴ` is a density
matrix for all source states. Positivity is automatic; the content is the trace. -/
theorem afnb_iff_density {I' O' J : ι → Type*} [∀ k, AddCommGroup (I' k)] [∀ k, Fintype (I' k)]
    [∀ k, DecidableEq (I' k)] [∀ k, Fintype (O' k)] [∀ k, DecidableEq (O' k)]
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (w : (∀ k, O' k) → (∀ k, I' k)) (K : ∀ k, J k → Matrix (O' k) (I' k) ℂ) :
    (∀ ρ, IsDensity ρ → born w ρ K = 1) ↔
      (∀ ρ, IsDensity ρ → IsDensity (indM w K * ρ * (indM w K)ᴴ)) := by
  constructor
  · intro h ρ hρ
    exact ⟨hρ.1.mul_mul_conjTranspose_same _, by rw [← born_eq_trace]; exact h ρ hρ⟩
  · intro h ρ hρ
    rw [born_eq_trace]; exact (h ρ hρ).2

end PFUL.Choi

#print axioms PFUL.Choi.born_anc_eq_one
#print axioms PFUL.Choi.bornC_anc_eq_one
#print axioms PFUL.Choi.afnb_iff_density
#print axioms PFUL.Choi.procMat_posSemidef
