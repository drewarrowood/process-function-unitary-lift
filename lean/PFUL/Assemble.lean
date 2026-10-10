import PFUL.Rows
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Countable alphabets: assembling the unitary on ℓ²
-/

open scoped InnerProductSpace ComplexConjugate

namespace PFUL.Countable

/-- **Completeness from Parseval on a separating family.** An orthonormal family `u` in a complex
inner-product space is total if there is a separating family `b` (only `0` is orthogonal to every
`b c`) such that Parseval holds at every `b c`. -/
theorem orthogonal_span_eq_bot {E R C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : R → E) (hu : Orthonormal ℂ u) (b : C → E)
    (hb : ∀ x, (∀ c, ⟪b c, x⟫_ℂ = 0) → x = 0)
    (hpar : ∀ c, HasSum (fun r => ‖⟪u r, b c⟫_ℂ‖ ^ 2) (‖b c‖ ^ 2)) :
    (Submodule.span ℂ (Set.range u))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hvu : ∀ r, ⟪u r, v⟫_ℂ = 0 := fun r =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self r)) hv
  by_contra hne
  set v' : E := ((‖v‖ : ℂ))⁻¹ • v with hv'
  have hvn : ‖v'‖ = 1 := norm_smul_inv_norm hne
  have hv'u : ∀ r, ⟪v', u r⟫_ℂ = 0 := by
    intro r; rw [hv', inner_smul_left, inner_eq_zero_symm.1 (hvu r), mul_zero]
  have huv' : ∀ r, ⟪u r, v'⟫_ℂ = 0 := by
    intro r; rw [hv', inner_smul_right, hvu r, mul_zero]
  let u' : Unit ⊕ R → E := Sum.elim (fun _ => v') u
  have hon : Orthonormal ℂ u' := by
    refine ⟨?_, ?_⟩
    · rintro (_ | r)
      · exact hvn
      · exact hu.1 r
    · rintro (_ | r) (_ | r') hij
      · exact absurd rfl hij
      · exact hv'u r'
      · exact huv' r
      · exact hu.2 (fun h => hij (congrArg Sum.inr h))
  have key : ∀ c, ⟪v', b c⟫_ℂ = 0 := by
    intro c
    have hB := hon.tsum_inner_products_le (x := b c)
    have hS : HasSum (fun i => ‖⟪u' i, b c⟫_ℂ‖ ^ 2) (‖⟪v', b c⟫_ℂ‖ ^ 2 + ‖b c‖ ^ 2) :=
      HasSum.sum (f := fun i => ‖⟪u' i, b c⟫_ℂ‖ ^ 2)
        (hasSum_single (f := fun _ : Unit => ‖⟪v', b c⟫_ℂ‖ ^ 2) () (fun b' hb' => absurd (Subsingleton.elim b' ()) hb'))
        (hpar c)
    rw [hS.tsum_eq] at hB
    have : ‖⟪v', b c⟫_ℂ‖ ^ 2 ≤ 0 := by linarith
    have h0 : ‖⟪v', b c⟫_ℂ‖ = 0 := by nlinarith [norm_nonneg ⟪v', b c⟫_ℂ]
    exact norm_eq_zero.1 h0
  have hv0 : v' = 0 := hb v' (fun c => by rw [← inner_conj_symm, key c, map_zero])
  rw [hv0, norm_zero] at hvn
  exact zero_ne_one hvn

open ENNReal in
lemma hasSum_real_of_ennreal {α : Type*} (g : α → NNReal) (h : ∑' a, (g a : ℝ≥0∞) = 1) :
    HasSum (fun a => (g a : ℝ)) 1 := by
  have hs : Summable g := ENNReal.tsum_coe_ne_top_iff_summable.1 (by rw [h]; exact ENNReal.one_ne_top)
  have h1 : ∑' a, g a = 1 := by
    have := ENNReal.coe_tsum hs
    rw [h] at this
    exact_mod_cast this
  have := (NNReal.hasSum_coe).2 hs.hasSum
  rw [h1, NNReal.coe_one] at this
  exact this

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}

open ENNReal in
/-- **The induced map is a unitary operator on ℓ² (countable alphabets).**
Hypotheses on each local kernel `V k` (countable index sets): square-summable orthonormal rows, and
unit-norm columns. Then there is a linear isometric equivalence `Φ : ℓ²(sources) ≃ ℓ²(sinks)` whose
matrix is the induced kernel `M (f,y) (e,x) = ∏ k, V k (f k, y k) (w f k + e k, x k)`:
`Φ v r = ∑' c, M r c * v c`, in particular `Φ (single c 1) r = M r c`. -/
theorem induced_unitary_l2 {X Y : ι → Type*} [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)]
    [∀ k, Countable (X k)] [∀ k, Countable (O k)] [∀ k, Countable (Y k)]
    [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (hcol : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 ≃ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      (∀ v r, HasSum (fun c => (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) * v c) (Φ v r)) ∧
      ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) := by
  classical
  set M : (∀ k, O k) × (∀ k, Y k) → (∀ k, I k) × (∀ k, X k) → ℂ :=
    fun r c => ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) with hM
  have hR : ∀ r r', HasSum (fun c => M r c * star (M r' c)) (if r = r' then 1 else 0) :=
    fun r r' => induced_rows w hw V hsq hrow r r'
  have hsq' : ∀ r, Summable fun c => ‖star (M r c)‖ ^ 2 := by
    intro r
    have h := (hR r r).summable
    have h2 : (fun c => M r c * star (M r c)) = fun c => ((‖M r c‖ ^ 2 : ℝ) : ℂ) := by
      funext c
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h2] at h
    simpa using Complex.summable_ofReal.1 h
  let u : (∀ k, O k) × (∀ k, Y k) → lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 := fun r =>
    ⟨fun c => star (M r c), memℓp_gen (by
      simpa [ENNReal.toReal_ofNat, Real.rpow_two] using hsq' r)⟩
  have hu_apply : ∀ r c, (u r : _ → ℂ) c = star (M r c) := fun r c => rfl
  have hinner : ∀ r (v : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2),
      HasSum (fun c => M r c * v c) ⟪u r, v⟫_ℂ := by
    intro r v
    have := lp.hasSum_inner (𝕜 := ℂ) (u r) v
    simpa [hu_apply, Complex.star_def, mul_comm] using this
  have hon : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro r r'
    have h1 := hinner r (u r')
    simp only [hu_apply] at h1
    exact h1.unique (hR r r')
  have hsp : (Submodule.span ℂ (Set.range u))ᗮ = ⊥ := by
    refine orthogonal_span_eq_bot u hon (fun c => lp.single 2 c (1 : ℂ)) ?_ ?_
    · intro x hx
      ext c
      have := hx c
      rw [lp.inner_single_left] at this
      simpa using this
    · intro c
      have hn : ‖(lp.single 2 c (1 : ℂ) : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2)‖ = 1 := by
        rw [lp.norm_single (by norm_num)]; simp
      rw [hn]
      have hcn := induced_colnorm w hw V hcol c.1 c.2
      have h := hasSum_real_of_ennreal (fun r => ‖M r c‖₊ ^ 2)
        (by simpa [ENNReal.coe_pow, hM] using hcn)
      have he : ∀ r, ⟪u r, (lp.single 2 c (1 : ℂ) : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2)⟫_ℂ = M r c := by
        intro r; rw [lp.inner_single_right]; simp [hu_apply, Complex.star_def]
      simpa [he] using h
  let B := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hB : ∀ r, (B r : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2) = u r := fun r => by
    simp [B, HilbertBasis.coe_mkOfOrthogonalEqBot]
  refine ⟨B.repr, fun v r => ?_, fun r c => ?_⟩
  · rw [HilbertBasis.repr_apply_apply, hB]; exact hinner r v
  · rw [HilbertBasis.repr_apply_apply, hB, lp.inner_single_right]
    simp [hu_apply, hM]

end PFUL.Countable

#print axioms PFUL.Countable.orthogonal_span_eq_bot
#print axioms PFUL.Countable.induced_unitary_l2
