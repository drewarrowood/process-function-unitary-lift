/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 11: the permutation/phase closed loop is automatically a bounded unitary of `ℓ²`

For any index set `X` (any cardinality, no countability, no measure) and any bijection
`e : X ≃ X` with a unit-modulus phase `φ`, the entrywise formula `(U ψ)(x) = φ(x) ψ(e x)`
defines a unitary (surjective linear isometry) of `ℓ²(X)` (`permPhaseUnitary`). No boundedness
is assumed: the map is defined pointwise and proved to land in `ℓ²` and preserve norms.

Corollary `closedLoop_l2_unitary`: for every process function `w` on abelian groups `G_k` of any
cardinality, the closed loop `(U ψ)(o) = φ(o) ψ(o - w o)` is a unitary of `ℓ²(∏ G_k)`.
-/
import PFUL.Continuous
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace PFUL.LiftAuto

variable {X : Type*}

theorem memℓp_permPhase (e : X ≃ X) {φ : X → ℂ} (h1 : ∀ x, ‖φ x‖ = 1)
    (f : lp (fun _ : X => ℂ) 2) : Memℓp (fun x => φ x * f (e x)) 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  simp only [norm_mul, h1, one_mul]
  exact e.summable_iff.2 hf

/-- The permutation/phase map as a linear isometry of `ℓ²(X)`. -/
noncomputable def permPhaseₗᵢ (e : X ≃ X) {φ : X → ℂ} (h1 : ∀ x, ‖φ x‖ = 1) :
    lp (fun _ : X => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : X => ℂ) 2 where
  toFun f := ⟨fun x => φ x * f (e x), memℓp_permPhase e h1 f⟩
  map_add' f g := by
    ext x
    show φ x * (f + g) (e x) = φ x * f (e x) + φ x * g (e x)
    simp [mul_add]
  map_smul' c f := by
    ext x
    show φ x * (c • f) (e x) = c * (φ x * f (e x))
    simp; ring
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change ∑' x, ‖φ x * f (e x)‖ ^ (2 : ENNReal).toReal = _
    simp only [norm_mul, h1, one_mul]
    exact e.tsum_eq (fun x => ‖f x‖ ^ (2 : ENNReal).toReal)

@[simp] theorem permPhaseₗᵢ_apply (e : X ≃ X) {φ : X → ℂ} (h1 : ∀ x, ‖φ x‖ = 1)
    (f : lp (fun _ : X => ℂ) 2) (x : X) : permPhaseₗᵢ e h1 f x = φ x * f (e x) := rfl

theorem permPhaseₗᵢ_surjective (e : X ≃ X) {φ : X → ℂ} (h1 : ∀ x, ‖φ x‖ = 1) :
    Function.Surjective (permPhaseₗᵢ e h1) := by
  have h1' : ∀ x, ‖(starRingEnd ℂ) (φ (e.symm x))‖ = 1 := fun x => by
    rw [Complex.norm_conj, h1]
  intro g
  refine ⟨permPhaseₗᵢ e.symm h1' g, ?_⟩
  ext x
  simp only [permPhaseₗᵢ_apply, Equiv.symm_apply_apply]
  rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1 x]; simp

/-- **Automatic boundedness**: `ψ ↦ φ · (ψ ∘ e)` is a unitary of `ℓ²(X)`, for any `X`. -/
noncomputable def permPhaseUnitary (e : X ≃ X) {φ : X → ℂ} (h1 : ∀ x, ‖φ x‖ = 1) :
    lp (fun _ : X => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : X => ℂ) 2 :=
  LinearIsometryEquiv.ofSurjective (permPhaseₗᵢ e h1) (permPhaseₗᵢ_surjective e h1)

/-- **Closed loop on `ℓ²` for groups of any cardinality.** For every process function `w`
and every unit-modulus phase `φ` (no measurability, countability or boundedness assumed),
`(U ψ)(o) = φ(o) ψ(o - w o)` is a unitary of `ℓ²(∏ G_k)`. -/
theorem closedLoop_l2_unitary {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ k, AddCommGroup (G k)] {w : (∀ k, G k) → (∀ k, G k)}
    (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w)
    {φ : (∀ k, G k) → ℂ} (h1 : ∀ x, ‖φ x‖ = 1) :
    ∃ U : lp (fun _ : (∀ k, G k) => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : (∀ k, G k) => ℂ) 2,
      ∀ ψ o, U ψ o = φ o * ψ (o - w o) :=
  ⟨permPhaseUnitary (Equiv.ofBijective _ (PFUL.Continuous.tau_bijective hw)) h1,
    fun _ _ => rfl⟩

end PFUL.LiftAuto
