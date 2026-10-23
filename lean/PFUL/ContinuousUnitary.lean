/-
F.5.5 (Lean, translation/point-move class): the closed loop of local unitaries that move
points by translation, decorated with arbitrary measurable unit-modulus phases,
  (U ψ)(o) = φ(o) · ψ(o - w o),
is a unitary operator on `L²(∏ G_k)` (a linear isometric equivalence), for every measurable
process function `w`.  Built from the Koopman operator of the measure-preserving bijection
`tau w` (F.5.3) and a phase multiplication operator.
-/
import PFUL.ContinuousMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option linter.unusedSectionVars false

namespace PFUL.Continuous

open MeasureTheory

section phase
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1)

include hφ h1 in
theorem memLp_phase (f : Lp ℂ 2 μ) : MemLp (fun x => φ x * f x) 2 μ :=
  (memLp_congr_norm (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f) (ae_of_all _ fun x => by simp [h1 x])).2 (Lp.memLp f)

/-- Multiplication by a unit-modulus measurable phase, as a linear isometry of `L²`. -/
noncomputable def phaseₗᵢ : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_phase hφ h1 f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_phase hφ h1 (f + g)), Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_phase hφ h1 f).toLp _) ((memLp_phase hφ h1 g).toLp _),
      MemLp.coeFn_toLp (memLp_phase hφ h1 f), MemLp.coeFn_toLp (memLp_phase hφ h1 g)]
      with x h1 h2 h3 h4 h5
    rw [h1, h3, h2, Pi.add_apply, Pi.add_apply, h4, h5, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_phase hφ h1 (c • f)), Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((memLp_phase hφ h1 f).toLp _), MemLp.coeFn_toLp (memLp_phase hφ h1 f)]
      with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, h2, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul,
      smul_eq_mul]; ring
  norm_map' f := by
    show ‖(memLp_phase hφ h1 f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable f) (ae_of_all _ fun x => by simp [h1 x])

theorem phaseₗᵢ_ae (f : Lp ℂ 2 μ) :
    (phaseₗᵢ hφ h1 f : X → ℂ) =ᵐ[μ] fun x => φ x * f x :=
  MemLp.coeFn_toLp (memLp_phase hφ h1 f)

include hφ h1 in
theorem phaseₗᵢ_surjective : Function.Surjective (phaseₗᵢ (μ := μ) hφ h1) := by
  have hc : Measurable fun x => (starRingEnd ℂ) (φ x) := by fun_prop
  have h1c : ∀ x, ‖(starRingEnd ℂ) (φ x)‖ = 1 := fun x => by rw [Complex.norm_conj, h1 x]
  intro g
  refine ⟨phaseₗᵢ hc h1c g, ?_⟩
  apply Lp.ext
  filter_upwards [phaseₗᵢ_ae hφ h1 (phaseₗᵢ hc h1c g), phaseₗᵢ_ae hc h1c g] with x ha hb
  rw [ha, hb, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1 x]; simp

/-- The phase operator as a unitary (linear isometric equivalence) of `L²`. -/
noncomputable def phaseUnitary : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (phaseₗᵢ hφ h1) (phaseₗᵢ_surjective hφ h1)
end phase

section koopman
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- Koopman operator of a measure-preserving measurable equivalence: a unitary of `L²`. -/
noncomputable def koopman (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he) (by
    intro g
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) g, ?_⟩
    show Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) g) = g
    rw [← Lp.compMeasurePreserving_comp_apply]
    have : (e.symm ∘ e : X → X) = id := funext e.symm_apply_apply
    simp only [this]
    exact Lp.compMeasurePreserving_id_apply g)

theorem koopman_ae (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (g : Lp ℂ 2 ν) :
    (koopman e he g : X → ℂ) =ᵐ[μ] fun x => g (e x) :=
  Lp.coeFn_compMeasurePreserving g he
end koopman

section loop
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ k, AddCommGroup (G k)] [∀ k, MeasurableSpace (G k)] [∀ k, MeasurableAdd (G k)]
    [∀ k, MeasurableSub₂ (G k)] [∀ k, StandardBorelSpace (G k)] (μ : ∀ k, Measure (G k))
    [∀ k, SigmaFinite (μ k)] [∀ k, (μ k).IsAddRightInvariant]
    {w : (∀ k, G k) → (∀ k, G k)}

/-- `tau w` as a measurable equivalence (Borel inverse by Lusin–Souslin). -/
noncomputable def tauEquiv (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) : (∀ k, G k) ≃ᵐ (∀ k, G k) where
  toEquiv := Equiv.ofBijective (tau w) (tau_bijective hw)
  measurable_toFun := tau_measurable hwm
  measurable_invFun := tauInv_measurable hwm hw

/-- **F.5.5 (Lean, translation class with phases).** For every measurable process function
`w` and every measurable unit-modulus phase `φ`, the closed loop
`(U ψ)(o) = φ(o) ψ(o - w o)` is a unitary of `L²(∏ G_k, ∏ μ_k)`. -/
theorem closedLoop_unitary (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w)
    {φ : (∀ k, G k) → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : Lp ℂ 2 (Measure.pi μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (Measure.pi μ),
      ∀ ψ, (U ψ : (∀ k, G k) → ℂ) =ᵐ[Measure.pi μ] fun o => φ o * ψ (tau w o) := by
  let e := tauEquiv hwm hw
  have he : MeasurePreserving e (Measure.pi μ) (Measure.pi μ) := tau_measurePreserving μ hwm hw
  refine ⟨(koopman e he).trans (phaseUnitary hφ h1), fun ψ => ?_⟩
  filter_upwards [phaseₗᵢ_ae hφ h1 (koopman e he ψ), koopman_ae e he ψ] with o ha hb
  show (phaseₗᵢ hφ h1 (koopman e he ψ) : _ → ℂ) o = _
  rw [ha, hb]; rfl
end loop

end PFUL.Continuous
