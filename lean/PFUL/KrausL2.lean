import PFUL.BornPairing

/-!
# Countable alphabets: general local channels (countably many Kraus operators)

A local channel `ρ ↦ ∑_y K_y ρ K_y†` on party `k` with countably many Kraus operators
`K_y : ℓ²(I_k × X_k) → ℓ²(O_k)` is encoded by its Stinespring kernel
`V k (o, y) (i, x) = ⟨o| K_y |i, x⟩` with the Kraus index `y` as output ancilla. Completeness
`∑_y K_y† K_y = 1` is exactly orthonormality of the columns of `V k` (`hiso`); the rows need not be
orthonormal (V k is an isometry, not a unitary).

* `induced_gram`: the induced kernel `M r c = ∏ₖ Vₖ(rₖ)(w r k + c k, …)` has orthonormal columns.
  Proof: polarization. For each pair of columns, build a four-column "polarized" kernel at each
  party whose columns all have unit norm, apply the unit-column theorem `induced_colnorm`, and
  recover `conj u · v = ½ ∑_φ conj(iᶠ) |(u + iᶠ v)/√2|²` pointwise.
* `induced_isometry_l2`: the induced operator is a linear isometry `ℓ²(sources × X) → ℓ²(sinks × Y)`.
* `valid_kraus_l2`: validity in density-operator form and in the Born-pairing form
  (`bornTerm`, see `PFUL/BornPairing.lean`) for arbitrary local channels with countably many
  Kraus operators. This extends `valid_born_l2`, which needed unitary kernels.
-/

open ContinuousLinearMap PFUL.TraceClass
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

namespace PFUL.Countable

section Aux

theorem star_mul_self_eq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

theorem hasSum_normSq_iff {R : Type*} (g : R → ℂ) :
    HasSum (fun r => star (g r) * g r) (1 : ℂ) ↔ ∑' r, ((‖g r‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
  simp_rw [star_mul_self_eq]
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, Complex.hasSum_ofReal]
  have e : ∀ r, ((‖g r‖₊ : ℝ≥0∞)) ^ 2 = ((‖g r‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := fun r => by push_cast; rfl
  simp_rw [e]
  have e2 : (fun r => ‖g r‖ ^ 2) = fun r => ((‖g r‖₊ ^ 2 : ℝ≥0) : ℝ) := by funext r; simp
  rw [e2, show (1 : ℝ) = ((1 : ℝ≥0) : ℝ) by simp, NNReal.hasSum_coe, ← ENNReal.hasSum_coe]
  constructor
  · intro h; simpa using h.tsum_eq
  · intro h; rw [ENNReal.coe_one, ← h]; exact ENNReal.summable.hasSum

theorem polar_id (u v s : ℂ) (hs : star s * s = 1 / 2) :
    star u * v = ∑ φ : Fin 4, star (Complex.I ^ (φ : ℕ)) / 2 *
      (star (s * (u + Complex.I ^ (φ : ℕ) * v)) * (s * (u + Complex.I ^ (φ : ℕ) * v))) := by
  simp only [Fin.sum_univ_four, star_mul', star_add, star_pow, Complex.star_def, Complex.conj_I,
    Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  simp only [Complex.star_def] at hs
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 2 * 3 by rfl, pow_mul, Complex.I_sq]; norm_num
  have h9 : Complex.I ^ 9 = Complex.I := by
    rw [show 9 = 4 * 2 + 1 by rfl, pow_add, pow_mul, Complex.I_pow_four]; simp
  have h3' : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  simp only [h6, h9, h3', Complex.I_sq, Complex.I_pow_four]
  ring_nf
  linear_combination (-2 * (starRingEnd ℂ) u * v) * hs

theorem star_I_pow_mul (n : ℕ) : star (Complex.I ^ n) * Complex.I ^ n = 1 := by
  rw [star_mul_self_eq, norm_pow, Complex.norm_I]; simp

theorem hasSum_polar {R : Type*} {u v : R → ℂ} {s φ : ℂ} (hs : star s * s = 1 / 2)
    (hφ : star φ * φ = 1)
    (hu : HasSum (fun r => star (u r) * u r) 1) (hv : HasSum (fun r => star (v r) * v r) 1)
    (huv : HasSum (fun r => star (u r) * v r) 0) (hvu : HasSum (fun r => star (v r) * u r) 0) :
    HasSum (fun r => star (s * (u r + φ * v r)) * (s * (u r + φ * v r))) 1 := by
  have h := (((hu.add (hv.mul_left (star φ * φ))).add (huv.mul_left φ)).add
    (hvu.mul_left (star φ))).mul_left (star s * s)
  convert h using 1
  · funext r; simp only [star_mul', star_add]; ring
  · rw [hs, hφ]; norm_num

end Aux

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type}

/-- **Orthonormal columns of the induced kernel** for isometric (Kraus/Stinespring) local kernels. -/
theorem induced_gram [∀ k, AddCommGroup (I k)] [∀ k, Countable (O k)] [∀ k, Countable (Y k)]
    [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0))
    (c c' : (∀ k, I k) × (∀ k, X k)) :
    HasSum (fun r : (∀ k, O k) × (∀ k, Y k) =>
      star (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
        ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c'.1 k, c'.2 k)) (if c = c' then 1 else 0) := by
  classical
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs_def
  have hs : star s * s = 1 / 2 := by
    rw [star_mul_self_eq, hs_def, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let same : ι → Prop := fun k => (c.1 k, c.2 k) = (c'.1 k, c'.2 k)
  let cw : ∀ k, Fin 4 → ℂ := fun k φ =>
    if same k then 1 / 4 else star (Complex.I ^ (φ : ℕ)) / 2
  let W : ∀ k, O k × Y k → I k × Fin 4 → ℂ := fun k r p =>
    if same k then V k r (p.1 + c.1 k, c.2 k)
    else s * (V k r (p.1 + c.1 k, c.2 k) + Complex.I ^ (p.2 : ℕ) * V k r (p.1 + c'.1 k, c'.2 k))
  have hW : ∀ k p, ∑' r, ((‖W k r p‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
    intro k p
    rw [← hasSum_normSq_iff]
    by_cases h : same k
    · simp only [W, h, ite_true]; simpa using hiso k (p.1 + c.1 k, c.2 k) (p.1 + c.1 k, c.2 k)
    · simp only [W, h, ite_false]
      have hne : (p.1 + c.1 k, c.2 k) ≠ (p.1 + c'.1 k, c'.2 k) := by
        intro he; apply h
        show (c.1 k, c.2 k) = (c'.1 k, c'.2 k)
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨add_left_cancel he.1, he.2⟩
      refine hasSum_polar hs (star_I_pow_mul _) ?_ ?_ ?_ ?_
      · simpa using hiso k (p.1 + c.1 k, c.2 k) (p.1 + c.1 k, c.2 k)
      · simpa using hiso k (p.1 + c'.1 k, c'.2 k) (p.1 + c'.1 k, c'.2 k)
      · simpa [hne] using hiso k (p.1 + c.1 k, c.2 k) (p.1 + c'.1 k, c'.2 k)
      · simpa [Ne.symm hne] using hiso k (p.1 + c'.1 k, c'.2 k) (p.1 + c.1 k, c.2 k)
  have hcol : ∀ φ : ι → Fin 4, HasSum (fun r : (∀ k, O k) × (∀ k, Y k) =>
      star (∏ k, W k (r.1 k, r.2 k) (w r.1 k + (0 : ∀ k, I k) k, φ k)) *
        ∏ k, W k (r.1 k, r.2 k) (w r.1 k + (0 : ∀ k, I k) k, φ k)) 1 := fun φ =>
    (hasSum_normSq_iff _).2 (induced_colnorm w hw W hW 0 φ)
  have hfac : ∀ k (r : O k × Y k) (i : I k),
      star (V k r (i + c.1 k, c.2 k)) * V k r (i + c'.1 k, c'.2 k) =
        ∑ φ : Fin 4, cw k φ * (star (W k r (i, φ)) * W k r (i, φ)) := by
    intro k r i
    by_cases h : same k
    · have h' : (i + c'.1 k, c'.2 k) = (i + c.1 k, c.2 k) := by
        simp only [same, Prod.mk.injEq] at h; rw [h.1, h.2]
      simp only [cw, W, h, ite_true, h', Fin.sum_univ_four]; ring
    · simp only [cw, W, h, ite_false]
      exact polar_id _ _ s hs
  have hpt : ∀ r : (∀ k, O k) × (∀ k, Y k),
      star (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
        ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c'.1 k, c'.2 k) =
      ∑ φ : ι → Fin 4, (∏ k, cw k (φ k)) *
        (star (∏ k, W k (r.1 k, r.2 k) (w r.1 k + (0 : ∀ k, I k) k, φ k)) *
          ∏ k, W k (r.1 k, r.2 k) (w r.1 k + (0 : ∀ k, I k) k, φ k)) := by
    intro r
    rw [star_prod, ← Finset.prod_mul_distrib]
    simp_rw [hfac]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr (by simp) fun φ _ => ?_
    rw [star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp
  have hsum := hasSum_sum (s := Finset.univ) fun φ (_ : φ ∈ Finset.univ) =>
    (hcol φ).mul_left (∏ k, cw k (φ k))
  convert hsum using 1
  · funext r; rw [hpt]
  · simp only [mul_one]
    rw [← Fintype.prod_sum]
    have hk : ∀ k, ∑ φ : Fin 4, cw k φ = if same k then 1 else 0 := by
      intro k
      by_cases h : same k
      · simp only [cw, h, ite_true, Fin.sum_univ_four]; norm_num
      · simp only [cw, h, ite_false, Fin.sum_univ_four, star_pow, Complex.star_def,
          Complex.conj_I]
        have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3]
        ring_nf; simp only [Complex.I_sq, pow_three, Complex.I_mul_I]; ring
    simp_rw [hk]
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies, Finset.prod_const_one]
    congr 1
    apply propext
    constructor
    · intro h k; subst h; rfl
    · intro h
      exact Prod.ext (funext fun k => congrArg Prod.fst (h k))
        (funext fun k => congrArg Prod.snd (h k))

end PFUL.Countable

namespace PFUL.Countable

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {I O X Y : ι → Type}

theorem inner_lp_eq_tsum {R : Type} (f g : lp (fun _ : R => ℂ) 2) :
    ⟪f, g⟫_ℂ = ∑' r, star (f r) * g r := by
  rw [lp.inner_eq_tsum]; congr 1; funext r; rw [mul_comm]; rfl

/-- **The induced operator is an isometry** for isometric local kernels (countably many Kraus
operators per party). `Φ (δ_c) = M(·, c)`. -/
theorem induced_isometry_l2 [∀ k, AddCommGroup (I k)] [∀ k, Countable (O k)]
    [∀ k, Countable (Y k)] [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) := by
  classical
  let M : (∀ k, I k) × (∀ k, X k) → (∀ k, O k) × (∀ k, Y k) → ℂ :=
    fun c r => ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)
  have hG := induced_gram w hw V hiso
  have hmem : ∀ c, Memℓp (M c) 2 := by
    intro c
    refine memℓp_gen ?_
    have h := hG c c
    simp_rw [star_mul_self_eq] at h
    have h' : Summable fun r => ‖M c r‖ ^ 2 :=
      Complex.summable_ofReal.1 h.summable
    simpa using h'
  let m : (∀ k, I k) × (∀ k, X k) → lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2 :=
    fun c => ⟨M c, hmem c⟩
  have hon : Orthonormal ℂ m := by
    rw [orthonormal_iff_ite]
    intro c c'
    rw [inner_lp_eq_tsum]
    exact (hG c c').tsum_eq
  refine ⟨hon.orthogonalFamily.linearIsometry, fun r c => ?_⟩
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [m, M]

theorem adjoint_comp_self_of_isometry {E F : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (U : E →ₗᵢ[ℂ] F) :
    adjoint U.toContinuousLinearMap ∘L U.toContinuousLinearMap = ContinuousLinearMap.id ℂ E := by
  ext x; refine ext_inner_left ℂ fun y => ?_
  simp

/-- **Validity on countable alphabets for general local channels** (countably many Kraus operators
per party, entangled/shared input ancillas folded into `ρ`). For every density operator `ρ` on
`ℓ²(sources × input ancillas)`: the global output `ΦρΦ†` and the sink state `Tr_Y(ΦρΦ†)` are density
operators, and the literal Born pairing `∑_r ⟪u_r, ρ u_r⟫` (row vectors `u_r` of `W = |U⟩⟩⟨⟨U|`,
entries `conj ∏ₖ Vₖ(…)`) has nonnegative terms and converges to `1 = Tr[Tr_Y(ΦρΦ†)]`. -/
theorem valid_kraus_l2 [∀ k, AddCommGroup (I k)] [∀ k, Countable (O k)]
    [∀ k, Countable (Y k)] [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      let U := Φ.toContinuousLinearMap
      (∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) ∧
      (∀ r c, rowVec U r c = star (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))) ∧
      ∀ ρ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
          lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2, IsDensity ρ →
        IsDensity (U ∘L ρ ∘L adjoint U) ∧ IsDensity (ptraceR (U ∘L ρ ∘L adjoint U)) ∧
        HasSum (bornTerm U ρ) 1 ∧ (∀ r, 0 ≤ bornTerm U ρ r) ∧
          ∑' r, bornTerm U ρ r = trace (ptraceR (U ∘L ρ ∘L adjoint U)) := by
  obtain ⟨Φ, hM⟩ := induced_isometry_l2 w hw V hiso
  refine ⟨Φ, ?_⟩
  intro U
  refine ⟨hM, fun r c => by rw [rowVec_apply]; exact congrArg star (hM r c), fun ρ hρ => ?_⟩
  have h1 := hρ.conj U (adjoint_comp_self_of_isometry Φ)
  have hs := hasSum_bornTerm U hρ.1
  rw [h1.2.2] at hs
  refine ⟨h1, h1.ptraceR, hs, fun r => bornTerm_nonneg _ hρ.2.1 r, ?_⟩
  rw [hs.tsum_eq, h1.ptraceR.2.2]

end PFUL.Countable

#print axioms PFUL.Countable.induced_gram
#print axioms PFUL.Countable.valid_kraus_l2
