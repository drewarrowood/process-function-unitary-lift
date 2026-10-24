/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 11: F.5.5 beyond global diffeomorphisms

Round 10 (`closedLoop_jacobian_unitary`) needed a global bijection, differentiable everywhere,
with nowhere-vanishing Jacobian. Here:

* `densityIsoₗᵢ`: multiplication by `√ρ` is a linear isometry `L²(ρμ) → L²(μ)` for **every**
  measurable `ρ ≥ 0` (zeros allowed).
* `closedLoop_isometry`: for any measurable map `g` (not necessarily injective or onto) with
  `g_*(ρμ) = μ`, `ψ ↦ φ · √ρ · (ψ ∘ g)` is a linear isometry of `L²(μ)`.
* `closedLoop_unitary_ae`: if moreover `g` is a measurable bijection and `ρ ≠ 0` only
  `μ`-almost everywhere, it is unitary.
* `closedLoop_jacobian_isometry`: `g` differentiable (within `s`) and injective only on a
  conull measurable set `s`, with conull image, Jacobian allowed to vanish: isometry with weight
  `√|det g'|`.
* `closedLoop_jacobian_unitary_ae`: a measurable bijection that is differentiable off a null set
  (piecewise smooth maps, e.g. threshold/Lugano lifts), maps the exceptional null set to a null
  set (Lusin's property (N); needed: a singular homeomorphism such as Minkowski's `?` is
  differentiable a.e. but blows a null set up to full measure), and has Jacobian nonzero almost
  everywhere, gives a unitary.
-/
import PFUL.ContinuousJacobian

set_option linter.unusedSectionVars false

namespace PFUL.Continuous

open MeasureTheory
open scoped ENNReal NNReal

section iso
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ : X → ℝ≥0} (hρ : Measurable ρ)

local notation "ν" => μ.withDensity (fun x => (ρ x : ℝ≥0∞))

theorem sqd_eq_zero_iff (x : X) : sqd ρ x = 0 ↔ ρ x = 0 := by
  simp [sqd]

include hρ in
/-- A `ρμ`-a.e. statement holds `μ`-a.e. wherever `√ρ ≠ 0`. -/
theorem ae_of_ae_withDensity {P : X → Prop} (h : ∀ᵐ x ∂ν, P x) :
    ∀ᵐ x ∂μ, sqd ρ x ≠ 0 → P x := by
  rw [ae_withDensity_iff (by fun_prop)] at h
  filter_upwards [h] with x hx hs
  exact hx (by rw [Ne, sqd_eq_zero_iff] at hs; exact_mod_cast hs)

include hρ in
theorem memLp_sqd' (f : Lp ℂ 2 ν) : MemLp (fun x => sqd ρ x * f x) 2 μ := by
  rw [memLp_iff, eLpNorm_sqd_mul hρ (Lp.stronglyMeasurable f).aestronglyMeasurable]
  exact Lp.memLp f

/-- Multiplication by `√ρ`, a linear isometry `L²(ρμ) → L²(μ)`, for any measurable `ρ ≥ 0`. -/
noncomputable def densityIsoₗᵢ : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_sqd' hρ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_sqd' hρ (f + g)),
      ae_of_ae_withDensity hρ (Lp.coeFn_add f g),
      Lp.coeFn_add ((memLp_sqd' hρ f).toLp _) ((memLp_sqd' hρ g).toLp _),
      MemLp.coeFn_toLp (memLp_sqd' hρ f), MemLp.coeFn_toLp (memLp_sqd' hρ g)]
      with x h1 h2 h3 h4 h5
    rw [h1, h3, Pi.add_apply, h4, h5]
    by_cases hs : sqd ρ x = 0
    · simp [hs]
    · rw [h2 hs, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_sqd' hρ (c • f)),
      ae_of_ae_withDensity hρ (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((memLp_sqd' hρ f).toLp _), MemLp.coeFn_toLp (memLp_sqd' hρ f)]
      with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4, smul_eq_mul]
    by_cases hs : sqd ρ x = 0
    · simp [hs]
    · rw [h2 hs, Pi.smul_apply, smul_eq_mul]; ring
  norm_map' f := by
    show ‖(memLp_sqd' hρ f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_sqd_mul hρ (Lp.stronglyMeasurable f).aestronglyMeasurable

theorem densityIsoₗᵢ_ae (f : Lp ℂ 2 ν) :
    (densityIsoₗᵢ hρ f : X → ℂ) =ᵐ[μ] fun x => sqd ρ x * f x :=
  MemLp.coeFn_toLp (memLp_sqd' hρ f)

include hρ in
/-- With `ρ ≠ 0` almost everywhere, `√ρ`-multiplication is onto. -/
theorem densityIsoₗᵢ_surjective (hpos : ∀ᵐ x ∂μ, ρ x ≠ 0) :
    Function.Surjective (densityIsoₗᵢ (μ := μ) hρ) := by
  intro h
  have hm' : AEStronglyMeasurable (fun x => h x * (sqd ρ x)⁻¹) μ :=
    (Lp.aestronglyMeasurable h).mul (measurable_sqd hρ).inv.aestronglyMeasurable
  have hmem : MemLp (fun x => h x * (sqd ρ x)⁻¹) 2 ν := by
    rw [memLp_iff, ← eLpNorm_sqd_mul hρ hm']
    have : (fun x => sqd ρ x * (h x * (sqd ρ x)⁻¹)) =ᵐ[μ] fun x => h x := by
      filter_upwards [hpos] with x hx
      have : sqd ρ x ≠ 0 := by rw [Ne, sqd_eq_zero_iff]; exact hx
      field_simp
    rw [eLpNorm_congr_ae this]; exact Lp.memLp h
  refine ⟨hmem.toLp _, ?_⟩
  apply Lp.ext
  have hae := ae_of_ae_withDensity hρ (MemLp.coeFn_toLp hmem)
  filter_upwards [densityIsoₗᵢ_ae hρ (hmem.toLp _), hae, hpos] with x h1 h2 hx
  have hs : sqd ρ x ≠ 0 := by rw [Ne, sqd_eq_zero_iff]; exact hx
  rw [h1, h2 hs]; field_simp

include hρ in
/-- **Closed loop for any measurable map with a Jacobian density, zeros allowed**: an isometry. -/
theorem closedLoop_isometry (g : X → X) (hg : MeasurePreserving g ν μ)
    {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : X → ℂ) =ᵐ[μ] fun o => φ o * (sqd ρ o * ψ (g o)) := by
  refine ⟨(phaseₗᵢ hφ h1).comp ((densityIsoₗᵢ hρ).comp (Lp.compMeasurePreservingₗᵢ ℂ g hg)),
    fun ψ => ?_⟩
  have hk := ae_of_ae_withDensity hρ (Lp.coeFn_compMeasurePreserving ψ hg)
  filter_upwards [phaseₗᵢ_ae hφ h1 (densityIsoₗᵢ hρ (Lp.compMeasurePreservingₗᵢ ℂ g hg ψ)),
    densityIsoₗᵢ_ae hρ (Lp.compMeasurePreservingₗᵢ ℂ g hg ψ), hk] with o ha hb hc
  show (phaseₗᵢ hφ h1 (densityIsoₗᵢ hρ (Lp.compMeasurePreservingₗᵢ ℂ g hg ψ)) : X → ℂ) o = _
  rw [ha, hb]
  by_cases hs : sqd ρ o = 0
  · simp [hs]
  · rw [show (Lp.compMeasurePreservingₗᵢ ℂ g hg ψ : X → ℂ) o = _ from hc hs]; rfl

include hρ in
/-- **Unitary closed loop with an a.e.-positive Jacobian density.** -/
theorem closedLoop_unitary_ae (hpos : ∀ᵐ x ∂μ, ρ x ≠ 0) (g : X ≃ᵐ X)
    (hg : MeasurePreserving g ν μ) {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : X → ℂ) =ᵐ[μ] fun o => φ o * (sqd ρ o * ψ (g o)) := by
  let D : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
    LinearIsometryEquiv.ofSurjective (densityIsoₗᵢ hρ) (densityIsoₗᵢ_surjective hρ hpos)
  refine ⟨((koopman g hg).trans D).trans (phaseUnitary hφ h1), fun ψ => ?_⟩
  have hk := ae_of_ae_withDensity hρ (koopman_ae g hg ψ)
  filter_upwards [phaseₗᵢ_ae hφ h1 (densityIsoₗᵢ hρ (koopman g hg ψ)),
    densityIsoₗᵢ_ae hρ (koopman g hg ψ), hk] with o ha hb hc
  show (phaseₗᵢ hφ h1 (densityIsoₗᵢ hρ (koopman g hg ψ)) : X → ℂ) o = _
  rw [ha, hb]
  by_cases hs : sqd ρ o = 0
  · simp [hs]
  · rw [hc hs]

end iso

section jacobian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The Jacobian density as an `ℝ≥0`-valued function. -/
noncomputable def jacD (g' : E → E →L[ℝ] E) (x : E) : ℝ≥0 := ⟨|(g' x).det|, abs_nonneg _⟩

theorem sqd_jacD (g' : E → E →L[ℝ] E) (x : E) :
    sqd (jacD g') x = (Real.sqrt |(g' x).det| : ℂ) := by
  have hs : ((NNReal.sqrt (jacD g' x) : ℝ)) = √|(g' x).det| := Real.coe_sqrt.trans rfl
  simp only [sqd, hs]

/-- Change of variables on a conull set: `g_*(|det g'| μ) = μ`. -/
theorem measurePreserving_jac (g : E → E) (hgm : Measurable g) (g' : E → E →L[ℝ] E)
    {s : Set E} (hs : MeasurableSet s) (hsc : μ sᶜ = 0)
    (hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) (hinj : Set.InjOn g s)
    (himg : μ (g '' s)ᶜ = 0) :
    MeasurePreserving g (μ.withDensity fun x => (jacD g' x : ℝ≥0∞)) μ := by
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet hg' hinj
  have hr : μ.restrict s = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hsc)
  have hr' : μ.restrict (g '' s) = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact himg)
  rw [hr, hr'] at hmap
  have hdens : (fun x => ENNReal.ofReal |(g' x).det|) = fun x => (jacD g' x : ℝ≥0∞) := by
    funext x; simp only [ENNReal.ofReal, Real.toNNReal_of_nonneg (abs_nonneg _)]; rfl
  rw [hdens] at hmap
  exact ⟨hgm, hmap⟩

/-- **F.5.5, local form, degenerate Jacobians allowed**: if `g` is measurable, injective and
differentiable (within `s`) on a conull measurable set `s` with conull image, then
`ψ ↦ φ · √|det g'| · (ψ ∘ g)` is a linear isometry of `L²(μ)`. -/
theorem closedLoop_jacobian_isometry (g : E → E) (hgm : Measurable g) (g' : E → E →L[ℝ] E)
    {s : Set E} (hs : MeasurableSet s) (hsc : μ sᶜ = 0)
    (hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) (hinj : Set.InjOn g s)
    (himg : μ (g '' s)ᶜ = 0) (hdm : Measurable fun x => |(g' x).det|)
    {φ : E → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : E → ℂ) =ᵐ[μ] fun o =>
        φ o * ((Real.sqrt |(g' o).det| : ℂ) * ψ (g o)) := by
  have hρ : Measurable (jacD g') := hdm.subtype_mk
  obtain ⟨U, hU⟩ := closedLoop_isometry hρ g
    (measurePreserving_jac μ g hgm g' hs hsc hg' hinj himg) hφ h1
  exact ⟨U, fun ψ => (hU ψ).trans (ae_of_all _ fun o => by simp only [sqd_jacD])⟩

/-- **F.5.5 for piecewise-smooth bijections**: a measurable bijection that is differentiable
(within `s`) on a conull measurable set `s` whose image is conull (property (N) for `sᶜ`), with
Jacobian nonzero almost everywhere, gives a unitary closed loop `ψ ↦ φ · √|det g'| · (ψ ∘ g)`. -/
theorem closedLoop_jacobian_unitary_ae (g : E ≃ᵐ E) (g' : E → E →L[ℝ] E)
    {s : Set E} (hs : MeasurableSet s) (hsc : μ sᶜ = 0)
    (hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) (himg : μ (g '' s)ᶜ = 0)
    (hdet : ∀ᵐ x ∂μ, (g' x).det ≠ 0)
    (hdm : Measurable fun x => |(g' x).det|)
    {φ : E → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : E → ℂ) =ᵐ[μ] fun o =>
        φ o * ((Real.sqrt |(g' o).det| : ℂ) * ψ (g o)) := by
  have hρ : Measurable (jacD g') := hdm.subtype_mk
  have hpos : ∀ᵐ x ∂μ, jacD g' x ≠ 0 := by
    filter_upwards [hdet] with x hx
    intro h0; apply hx; have := congrArg Subtype.val h0; simpa [jacD] using this
  obtain ⟨U, hU⟩ := closedLoop_unitary_ae hρ hpos g
    (measurePreserving_jac μ g g.measurable g' hs hsc hg' g.injective.injOn himg) hφ h1
  exact ⟨U, fun ψ => (hU ψ).trans (ae_of_all _ fun o => by simp only [sqd_jacD])⟩

end jacobian

end PFUL.Continuous
