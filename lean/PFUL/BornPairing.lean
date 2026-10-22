import PFUL.TraceValidity

/-!
# Countable alphabets: the literal Born-rule pairing `Tr[W (ρ ⊗ 1 ⊗ ⨂ C_k)ᵀ] = 1`

For infinite alphabets the process operator `W = |U⟩⟩⟨⟨U|` and the local Choi operators are not
trace class (e.g. `Tr W = ∑_{r,c} |M r c|² = ∞`), so `Tr[W ⋯]` cannot be read as the trace of a
product of trace-class operators. The honest formulation used here:

* `W` is kept as what it is in finite dimensions, the family of its row vectors
  `u_r = ⟨⟨U| e_r⟩` with entries `u_r c = conj (M r c)` (`rowVec_apply`); equivalently `W` is the
  sesquilinear form `(ρ) ↦ ∑_r ⟪u_r, ρ u_r⟫`.
* The pairing of `W` with an input density operator `ρ` (source ⊗ input ancillas; the local
  channels are already inside `M`, as in `PFUL.Choi.born_eq_trace`) is the series over sink
  outcomes `r = (o, y)` of `bornTerm U ρ r = ⟪u_r, ρ u_r⟫`, i.e. **the limit of the finite
  truncations** `∑_{r ∈ F} ⟪u_r, ρ u_r⟫` over finite sets `F` of sink outcomes (Mathlib's
  `HasSum` is exactly convergence of this net of truncations, unconditionally).
* In finite dimensions this series is a finite sum and equals `Tr[W(ρ ⊗ 1 ⊗ ⨂ C_k)ᵀ]`
  (`PFUL.Choi.born_eq_trace`). Here it is proved to converge (absolutely, every term is ≥ 0) to
  `Tr[Tr_Y(UρU†)] = 1`, which is the statement `valid_density_l2`.
-/

open ContinuousLinearMap PFUL.TraceClass
open scoped InnerProductSpace ComplexOrder
set_option linter.unusedSectionVars false

universe u

namespace PFUL.Countable

section General
variable {S R : Type u} [DecidableEq S] [DecidableEq R]

/-- Row vector `u_r = U† e_r` of the induced operator (the `r`-th block of `|U⟩⟩`). -/
noncomputable def rowVec (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2) (r : R) :
    lp (fun _ : S => ℂ) 2 :=
  adjoint U (lp.single 2 r 1)

theorem inner_single_left' {T : Type u} [DecidableEq T] (t : T) (f : lp (fun _ : T => ℂ) 2) :
    ⟪lp.single 2 t (1 : ℂ), f⟫_ℂ = f t := by
  rw [lp.inner_single_left]; simp

theorem rowVec_apply (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2) (r : R) (c : S) :
    rowVec U r c = star (U (lp.single 2 c 1) r) := by
  rw [← inner_single_left', rowVec, adjoint_inner_right, ← inner_conj_symm, inner_single_left']
  rfl

/-- One term of the Born pairing of `W = |U⟩⟩⟨⟨U|` with `ρ`: `⟪u_r, ρ u_r⟫`. -/
noncomputable def bornTerm (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (ρ : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : S => ℂ) 2) (r : R) : ℂ :=
  ⟪rowVec U r, ρ (rowVec U r)⟫_ℂ

theorem bornTerm_eq (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (ρ : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : S => ℂ) 2) (r : R) :
    bornTerm U ρ r = ⟪lp.single 2 r (1 : ℂ), (U ∘L ρ ∘L adjoint U) (lp.single 2 r 1)⟫_ℂ := by
  simp only [comp_apply]; rw [← adjoint_inner_left]; rfl

theorem stdBasis_lp_apply {T : Type u} [DecidableEq T] (t : T) :
    (default : HilbertBasis T ℂ (lp (fun _ : T => ℂ) 2)) t = lp.single 2 t 1 := by
  rw [← HilbertBasis.repr_symm_single]; rfl

/-- Terms are real and nonnegative for positive `ρ`. -/
theorem bornTerm_nonneg (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    {ρ : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : S => ℂ) 2} (hρ : ρ.IsPositive) (r : R) :
    0 ≤ bornTerm U ρ r :=
  hρ.inner_nonneg_right (rowVec U r)

/-- **The truncations of the Born pairing converge to the trace of the output state.** -/
theorem hasSum_bornTerm (U : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    {ρ : lp (fun _ : S => ℂ) 2 →L[ℂ] lp (fun _ : S => ℂ) 2} (hρ : ρ ∈ traceClass _) :
    HasSum (bornTerm U ρ) (trace (U ∘L ρ ∘L adjoint U)) := by
  have h := hasSum_trace (conj_mem U hρ) (default : HilbertBasis R ℂ (lp (fun _ : R => ℂ) 2))
  simp only [stdBasis_lp_apply] at h
  convert h using 1
  funext r; exact bornTerm_eq U ρ r

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type}

/-- **Literal validity, countable alphabets.** Same hypotheses as `valid_density_l2`. The induced
unitary `Φ` has matrix entries `M r c = ∏ₖ Vₖ(⋯)`; its row vectors `u_r` (the blocks of
`W = |U⟩⟩⟨⟨U|`) have entries `conj (M r c)`; and for every density operator `ρ` the Born pairing
`∑_{r = (o,y)} ⟪u_r, ρ u_r⟫` (sum over sink outputs and output ancillas, i.e. `1_Y` on the output
ancillas) converges, as the limit of its finite truncations, to `1`, with nonnegative terms, and
its value is `Tr[Tr_Y(ΦρΦ†)]` from `valid_density_l2`. -/
theorem valid_born_l2 {X Y : ι → Type} [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)]
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
      let U : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2 := Φ
      (∀ r c, rowVec U r c = star (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))) ∧
      ∀ ρ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
          lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2, IsDensity ρ →
        HasSum (bornTerm U ρ) 1 ∧ (∀ r, 0 ≤ bornTerm U ρ r) ∧
          ∑' r, bornTerm U ρ r = trace (ptraceR (U ∘L ρ ∘L adjoint U)) := by
  obtain ⟨Φ, hM, hval⟩ := valid_density_l2 w hw V hsq hrow hcol
  refine ⟨Φ, ?_⟩
  intro U
  refine ⟨fun r c => by rw [rowVec_apply]; exact congrArg star (hM r c), fun ρ hρ => ?_⟩
  obtain ⟨h1, -, h3⟩ := hval ρ hρ
  have hs := hasSum_bornTerm U hρ.1
  rw [h1.2.2] at hs
  refine ⟨hs, fun r => bornTerm_nonneg _ hρ.2.1 r, ?_⟩
  rw [hs.tsum_eq, h3]

end PFUL.Countable

#print axioms PFUL.Countable.valid_born_l2
