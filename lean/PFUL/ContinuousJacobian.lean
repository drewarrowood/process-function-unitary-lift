/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 10: F.5.5 for general point maps (change of variables)

If a measurable bijection `g` carries `ρ·μ` to `μ` (`MeasurePreserving g (μ.withDensity ρ) μ`,
i.e. `ρ` is the Jacobian of `g`), with `ρ > 0`, then for every unit-modulus measurable phase `φ`

  `(U ψ)(o) = φ(o) · √ρ(o) · ψ(g o)`

is a unitary of `L²(μ)`. With `ρ = |det g'|` this is the change-of-variables form of F.5.5
(`closedLoop_jacobian_unitary`, via Mathlib's `map_withDensity_abs_det_fderiv_eq_addHaar`).
-/
import PFUL.ContinuousUnitary
import Mathlib.MeasureTheory.Function.Jacobian

set_option linter.unusedSectionVars false

namespace PFUL.Continuous

open MeasureTheory
open scoped ENNReal NNReal

section density
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ : X → ℝ≥0}
  (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)

/-- `√ρ` as a complex function. -/
noncomputable def sqd (ρ : X → ℝ≥0) (x : X) : ℂ := ((NNReal.sqrt (ρ x) : ℝ) : ℂ)

theorem sqd_ne_zero (hpos : ∀ x, 0 < ρ x) (x : X) : sqd ρ x ≠ 0 := by
  simp [sqd, (hpos x).ne']

theorem measurable_sqd (hρ : Measurable ρ) : Measurable (sqd ρ) := by
  unfold sqd; fun_prop

theorem enorm_sqd_sq (x : X) : ‖sqd ρ x‖ₑ ^ (2 : ℝ) = (ρ x : ℝ≥0∞) := by
  have h : ‖sqd ρ x‖ₑ = ((NNReal.sqrt (ρ x) : ℝ≥0) : ℝ≥0∞) := by
    simp only [sqd]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal]
  rw [h, ENNReal.rpow_two, ← ENNReal.coe_pow, NNReal.sq_sqrt]

theorem ac_withDensity (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
    μ ≪ μ.withDensity (fun x => (ρ x : ℝ≥0∞)) :=
  withDensity_absolutelyContinuous' (by fun_prop) (ae_of_all _ fun x => by simp [(hpos x).ne'])

include hρ in
/-- The change-of-density identity for `L²` norms. -/
theorem eLpNorm_sqd_mul {F : X → ℂ} (hF : AEStronglyMeasurable F μ) :
    eLpNorm (fun x => sqd ρ x * F x) 2 μ =
      eLpNorm F 2 (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) := by
  have hF' : AEStronglyMeasurable F (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun x => sqd ρ x * F x) two_ne_zero
      ENNReal.ofNat_ne_top ((measurable_sqd hρ).aestronglyMeasurable.mul hF),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hF',
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop)
      (ae_of_all _ fun x => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sqd_sq]

end density

section loop
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ : X → ℝ≥0}
  (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)

local notation "ν" => μ.withDensity (fun x => (ρ x : ℝ≥0∞))

include hρ hpos in
theorem memLp_sqd (f : Lp ℂ 2 ν) : MemLp (fun x => sqd ρ x * f x) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => f x) μ :=
    (Lp.aestronglyMeasurable f).mono_ac (ac_withDensity hρ hpos)
  rw [memLp_iff, eLpNorm_sqd_mul hρ hm]; exact Lp.memLp f

include hρ hpos in
theorem memLp_sqd_inv (h : Lp ℂ 2 μ) : MemLp (fun x => h x * (sqd ρ x)⁻¹) 2 ν := by
  have hm : AEStronglyMeasurable (fun x => h x * (sqd ρ x)⁻¹) μ :=
    (Lp.aestronglyMeasurable h).mul (measurable_sqd hρ).inv.aestronglyMeasurable
  rw [memLp_iff, ← eLpNorm_sqd_mul hρ hm]
  have : (fun x => sqd ρ x * (h x * (sqd ρ x)⁻¹)) = fun x => h x := by
    funext x; field_simp [sqd_ne_zero hpos x]
  rw [this]; exact Lp.memLp h

/-- Multiplication by `√ρ`, a linear isometry `L²(ρμ) → L²(μ)`. -/
noncomputable def densityₗᵢ : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_sqd hρ hpos f).toLp _
  map_add' f g := by
    apply Lp.ext
    have hae := (ac_withDensity hρ hpos).ae_le (Lp.coeFn_add f g)
    filter_upwards [MemLp.coeFn_toLp (memLp_sqd hρ hpos (f + g)), hae,
      Lp.coeFn_add ((memLp_sqd hρ hpos f).toLp _) ((memLp_sqd hρ hpos g).toLp _),
      MemLp.coeFn_toLp (memLp_sqd hρ hpos f), MemLp.coeFn_toLp (memLp_sqd hρ hpos g)]
      with x h1 h2 h3 h4 h5
    rw [h1, h3, h2, Pi.add_apply, Pi.add_apply, h4, h5, mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hae := (ac_withDensity hρ hpos).ae_le (Lp.coeFn_smul c f)
    filter_upwards [MemLp.coeFn_toLp (memLp_sqd hρ hpos (c • f)), hae,
      Lp.coeFn_smul c ((memLp_sqd hρ hpos f).toLp _), MemLp.coeFn_toLp (memLp_sqd hρ hpos f)]
      with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, h2, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul,
      smul_eq_mul]; ring
  norm_map' f := by
    show ‖(memLp_sqd hρ hpos f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_sqd_mul hρ ((Lp.aestronglyMeasurable f).mono_ac (ac_withDensity hρ hpos))

theorem densityₗᵢ_ae (f : Lp ℂ 2 ν) :
    (densityₗᵢ hρ hpos f : X → ℂ) =ᵐ[μ] fun x => sqd ρ x * f x :=
  MemLp.coeFn_toLp (memLp_sqd hρ hpos f)

include hρ hpos in
theorem densityₗᵢ_surjective : Function.Surjective (densityₗᵢ (μ := μ) hρ hpos) := by
  intro h
  refine ⟨(memLp_sqd_inv hρ hpos h).toLp _, ?_⟩
  apply Lp.ext
  have hae := (ac_withDensity hρ hpos).ae_le (MemLp.coeFn_toLp (memLp_sqd_inv hρ hpos h))
  filter_upwards [densityₗᵢ_ae hρ hpos ((memLp_sqd_inv hρ hpos h).toLp _), hae] with x h1 h2
  rw [h1, h2]; field_simp [sqd_ne_zero hpos x]

/-- `√ρ` multiplication as a unitary `L²(ρμ) ≃ L²(μ)`. -/
noncomputable def densityUnitary : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (densityₗᵢ hρ hpos) (densityₗᵢ_surjective hρ hpos)

include hρ hpos in
/-- **F.5.5 for general point maps.** If the measurable bijection `g` pushes `ρ·μ` to `μ`
(`ρ > 0` is the Jacobian), then `ψ ↦ φ · √ρ · (ψ ∘ g)` is a unitary of `L²(μ)` for every
unit-modulus measurable phase `φ`. -/
theorem closedLoop_general_unitary (g : X ≃ᵐ X) (hg : MeasurePreserving g ν μ)
    {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : X → ℂ) =ᵐ[μ] fun o => φ o * (sqd ρ o * ψ (g o)) := by
  refine ⟨((koopman g hg).trans (densityUnitary hρ hpos)).trans (phaseUnitary hφ h1),
    fun ψ => ?_⟩
  have hk := (ac_withDensity hρ hpos).ae_le (koopman_ae g hg ψ)
  filter_upwards [phaseₗᵢ_ae hφ h1 (densityₗᵢ hρ hpos (koopman g hg ψ)),
    densityₗᵢ_ae hρ hpos (koopman g hg ψ), hk] with o ha hb hc
  show (phaseₗᵢ hφ h1 (densityₗᵢ hρ hpos (koopman g hg ψ)) : X → ℂ) o = _
  rw [ha, hb, hc]

end loop

section jacobian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **F.5.5, change-of-variables form.** For a measurable bijection `g` of a finite-dimensional
real space with derivative `g'` everywhere and nowhere-vanishing, measurable Jacobian, the
closed loop `ψ ↦ φ · √|det g'| · (ψ ∘ g)` is a unitary of `L²(μ)`. -/
theorem closedLoop_jacobian_unitary (g : E ≃ᵐ E) (g' : E → E →L[ℝ] E)
    (hg' : ∀ x, HasFDerivAt g (g' x) x) (hdet : ∀ x, (g' x).det ≠ 0)
    (hdm : Measurable fun x => |(g' x).det|)
    {φ : E → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ ψ, (U ψ : E → ℂ) =ᵐ[μ] fun o =>
        φ o * ((Real.sqrt |(g' o).det| : ℂ) * ψ (g o)) := by
  set ρ : E → ℝ≥0 := fun x => ⟨|(g' x).det|, abs_nonneg _⟩ with hρdef
  have hρ : Measurable ρ := hdm.subtype_mk
  have hpos : ∀ x, 0 < ρ x := fun x => by
    show (0 : ℝ) < |(g' x).det|; exact abs_pos.2 (hdet x)
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar μ MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hg' x).hasFDerivWithinAt) (g.injective.injOn)
  rw [Measure.restrict_univ, Set.image_univ, g.surjective.range_eq, Measure.restrict_univ] at hmap
  have hdens : (fun x => ENNReal.ofReal |(g' x).det|) = fun x => (ρ x : ℝ≥0∞) := by
    funext x; simp only [ENNReal.ofReal, Real.toNNReal_of_nonneg (abs_nonneg _)]; rfl
  rw [hdens] at hmap
  have hg : MeasurePreserving g (μ.withDensity fun x => (ρ x : ℝ≥0∞)) μ :=
    ⟨g.measurable, hmap⟩
  obtain ⟨U, hU⟩ := closedLoop_general_unitary hρ hpos g hg hφ h1
  refine ⟨U, fun ψ => (hU ψ).trans (ae_of_all _ fun o => ?_)⟩
  have hs : ((NNReal.sqrt (ρ o) : ℝ)) = √|(g' o).det| := Real.coe_sqrt.trans rfl
  simp only [sqd, hs]

end jacobian

end PFUL.Continuous
