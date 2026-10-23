/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 10: the Switchboard loop is unitary for countable ancillas

`CounterexampleInf` proved the closed loop is an isometry of `ℓ²`. Here we prove that its
kernel also has orthonormal rows (via `row_scalar_key`), and that an isometry of `ℓ²` whose
kernel has orthonormal rows is surjective. Hence the loop is a unitary (`≃ₗᵢ`).
-/
import PFUL.CounterexampleRows

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

namespace PFUL.Counterexample

/-- A kernel with orthonormal rows. -/
def IsCoIsoKernel {X Y : Type} (a : Matrix Y X ℂ) [DecidableEq Y] : Prop :=
  ∀ r r', HasSum (fun c => a r c * star (a r' c)) (if r = r' then 1 else 0)

theorem entOp_adjoint {X : Type} [DecidableEq X] (A : L2 X →L[ℂ] L2 X) (r c : X) :
    entOp (ContinuousLinearMap.adjoint A) c r = star (entOp A r c) := by
  have h1 : entOp (ContinuousLinearMap.adjoint A) c r =
      ⟪lp.single 2 c (1 : ℂ), ContinuousLinearMap.adjoint A (lp.single 2 r (1 : ℂ))⟫_ℂ := by
    rw [lp.inner_single_left]; simp [entOp]
  rw [h1, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, lp.inner_single_left]
  simp [entOp]

/-- The kernel of a unitary has orthonormal rows. -/
theorem isCoIsoKernel_entOp {X : Type} [DecidableEq X] (A : L2 X →L[ℂ] L2 X)
    (hA : A ∈ unitary (L2 X →L[ℂ] L2 X)) : IsCoIsoKernel (entOp A) := by
  intro r r'
  have hA' : ContinuousLinearMap.adjoint A ∈ unitary (L2 X →L[ℂ] L2 X) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact Unitary.star_mem hA
  have h := isIsoKernel_entOp _ hA' r r'
  simp only [entOp_adjoint, star_star] at h
  exact h

theorem summable_sq_of_isCoIsoKernel {X Y : Type} [DecidableEq Y] {a : Matrix Y X ℂ}
    (ha : IsCoIsoKernel a) (r : Y) : Summable fun c => ‖a r c‖ ^ 2 := by
  have h := ha r r
  have h' : (fun c => a r c * star (a r c)) = fun c => ((‖a r c‖ ^ 2 : ℝ) : ℂ) := by
    funext c; rw [mul_comm, PFUL.Countable.star_mul_self_eq]
  rw [h'] at h
  exact Complex.summable_ofReal.1 h.summable

theorem xor_shift2 : ∀ u u' t : Fin 8, u' ^^^ t = (u ^^^ t) ^^^ (u ^^^ u') := by decide

theorem xor_invol : ∀ u t : Fin 8, u ^^^ (u ^^^ t) = t := by decide

set_option maxHeartbeats 4000000 in
/-- **Row orthonormality** of the Switchboard loop for arbitrary (countable) ancillas whose
local kernels have orthonormal rows. -/
theorem isCoIsoKernel_compose_Vsb {κ : Fin 3 → Type} [∀ k, DecidableEq (κ k)]
    (a : ∀ k, Matrix (Bool × κ k) (Bool × κ k) ℂ) (ha : ∀ k, IsCoIsoKernel (a k)) :
    IsCoIsoKernel (compose Vsb a) := by
  rintro ⟨⟨o, u⟩, β⟩ ⟨⟨o', u'⟩, β'⟩
  set R : Fin 3 → Bool → Bool → ℂ := fun k y z =>
    ∑' α : κ k, a k (bit k o, β k) (y, α) * star (a k (bit k o', β' k) (z, α)) with hRdef
  have hsn : ∀ k y z, Summable fun α : κ k =>
      ‖a k (bit k o, β k) (y, α) * star (a k (bit k o', β' k) (z, α))‖ := by
    intro k y z
    have := summable_star_mul
      ((summable_sq_of_isCoIsoKernel (ha k) (bit k o, β k)).comp_injective
        (Prod.mk_right_injective y))
      ((summable_sq_of_isCoIsoKernel (ha k) (bit k o', β' k)).comp_injective
        (Prod.mk_right_injective z))
    refine this.congr fun α => ?_
    simp only [norm_mul, norm_star]
  have hfib : ∀ k y z, HasSum (fun α : κ k => a k (bit k o, β k) (y, α) *
      star (a k (bit k o', β' k) (z, α))) (R k y z) := fun k y z => (hsn k y z).of_norm.hasSum
  have hR : ∀ k, R k false false + R k true true =
      if bit k o = bit k o' then (if β k = β' k then 1 else 0) else 0 := by
    intro k
    have h1 := (ha k (bit k o, β k) (bit k o', β' k)).prod_fiberwise fun y => hfib k y y
    have h2 := (hasSum_fintype fun y : Bool => R k y y).unique h1
    rw [Fintype.sum_bool] at h2
    rw [add_comm, h2]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  have hcol : ∀ s t : Fin 8, HasSum (fun α : (∀ k, κ k) =>
      compose Vsb a ((o, u), β) ((s, t), α) * star (compose Vsb a ((o', u'), β') ((s, t), α)))
      (board o (u ^^^ t) s * star (board o' (u' ^^^ t) s) *
        ∏ k, R k (bit k (u ^^^ t)) (bit k (u' ^^^ t))) := by
    intro s t
    obtain ⟨-, hp⟩ := hasSum_pi_prod 3
      (fun k α => a k (bit k o, β k) (bit k (u ^^^ t), α) *
        star (a k (bit k o', β' k) (bit k (u' ^^^ t), α)))
      (fun k => R k (bit k (u ^^^ t)) (bit k (u' ^^^ t)))
      (fun k => hsn k _ _) (fun k => hfib k _ _)
    convert hp.mul_left (board o (u ^^^ t) s * star (board o' (u' ^^^ t) s)) using 1
    funext α
    rw [compose_Vsb_apply, compose_Vsb_apply, star_mul, star_prod, Finset.prod_mul_distrib]
    ring
  have htot := hasSum_prod_fintype (fun q : (Fin 8 × Fin 8) × (∀ k, κ k) =>
      compose Vsb a ((o, u), β) q * star (compose Vsb a ((o', u'), β') q))
    (fun p : Fin 8 × Fin 8 => board o (u ^^^ p.2) p.1 * star (board o' (u' ^^^ p.2) p.1) *
        ∏ k, R k (bit k (u ^^^ p.2)) (bit k (u' ^^^ p.2)))
    fun p => hcol p.1 p.2
  convert htot using 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hsh : ∑ t : Fin 8, ∑ s : Fin 8, board o (u ^^^ t) s * star (board o' (u' ^^^ t) s) *
        ∏ k, R k (bit k (u ^^^ t)) (bit k (u' ^^^ t)) =
      ∑ e : Fin 8, ∑ s : Fin 8, board o e s * star (board o' (e ^^^ (u ^^^ u')) s) *
        ∏ k, R k (bit k e) (bit k (e ^^^ (u ^^^ u'))) := by
    simp_rw [xor_shift2 u u']
    exact Fintype.sum_equiv (Function.Involutive.toPerm (fun t => u ^^^ t) (xor_invol u)) _ _
      (fun t => rfl)
  rw [hsh, row_scalar_key R (fun k => if β k = β' k then 1 else 0) o o' (u ^^^ u') hR]
  simp only [xor_eq_zero_iff', Finset.prod_boole, Finset.mem_univ, true_implies, Prod.mk.injEq]
  have hβ : (∀ k, β k = β' k) ↔ β = β' := funext_iff.symm
  simp only [hβ]
  by_cases h1 : o = o' <;> by_cases h2 : u = u' <;> by_cases h3 : β = β' <;> simp [h1, h2, h3]

/-- An isometry of `ℓ²` whose kernel has orthonormal rows is surjective. -/
theorem surjective_of_isCoIsoKernel {X : Type} [DecidableEq X] (U : L2 X →ₗᵢ[ℂ] L2 X)
    (hrow : IsCoIsoKernel (fun r c => U (lp.single 2 c (1 : ℂ)) r)) : Function.Surjective U := by
  set T := U.toContinuousLinearMap with hT
  set S := ContinuousLinearMap.adjoint T with hSdef
  have hS : ∀ r c, S (lp.single 2 r (1 : ℂ)) c = star (U (lp.single 2 c (1 : ℂ)) r) := by
    intro r c
    have h1 : S (lp.single 2 r (1 : ℂ)) c =
        ⟪lp.single 2 c (1 : ℂ), S (lp.single 2 r (1 : ℂ))⟫_ℂ := by
      rw [lp.inner_single_left]; simp
    rw [h1, hSdef, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
      lp.inner_single_left]
    simp [T]
  have hbasis : ∀ r, T (S (lp.single 2 r (1 : ℂ))) = lp.single 2 r 1 := by
    intro r
    apply lp.ext; funext r'
    have h1 : T (S (lp.single 2 r (1 : ℂ))) r' =
        ⟪lp.single 2 r' (1 : ℂ), T (S (lp.single 2 r (1 : ℂ)))⟫_ℂ := by
      rw [lp.inner_single_left]; simp
    rw [h1, ← ContinuousLinearMap.adjoint_inner_left, ← hSdef]
    have h2 := hasSum_inner_lp (S (lp.single 2 r' (1 : ℂ))) (S (lp.single 2 r (1 : ℂ)))
    simp only [hS, star_star] at h2
    rw [h2.unique (hrow r' r), lp.single_apply, Pi.single_apply]
  have hall : ∀ f, T (S f) = f := by
    intro f
    have h1 := lp.hasSum_single (E := fun _ : X => ℂ) (p := 2) (by simp : (2 : ENNReal) ≠ ⊤) f
    have h2 := h1.mapL (T.comp S)
    have h3 : (fun i => (T.comp S) (lp.single 2 i (f i))) = fun i => lp.single 2 i (f i) := by
      funext i
      have : (lp.single 2 i (f i) : L2 X) = f i • (lp.single 2 i (1 : ℂ) : L2 X) := by
        rw [← lp.single_smul, smul_eq_mul, mul_one]
      rw [this, map_smul, ContinuousLinearMap.comp_apply, hbasis]
    rw [h3] at h2
    exact h2.unique h1
  intro f
  exact ⟨S f, hall f⟩

/-- **Unitary purity against countable ancillas**: the closed loop with any local unitaries on
`ℓ²(Bool × κ_k)` is a unitary (a surjective linear isometry) of `ℓ²(P × ∏ κ_k)` with matrix
`composeOp V A`. -/
def IsUnitaryInf {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, Countable (κ k)] [∀ k, DecidableEq (κ k)]
    (A : ∀ k, L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k)),
    (∀ k, A k ∈ unitary (L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k))) →
      ∃ U : L2 (P × (∀ k, κ k)) ≃ₗᵢ[ℂ] L2 (P × (∀ k, κ k)),
        ∀ r c, U (lp.single 2 c (1 : ℂ)) r = composeOp V A r c

theorem IsUnitaryInf.isPureInf {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsUnitaryInf V) : IsPureInf V := by
  intro κ _ _ A hA
  obtain ⟨U, hU⟩ := h κ A hA
  exact ⟨U.toLinearIsometry, hU⟩

/-- **The Switchboard is unitary against countable ancillas.** -/
theorem isUnitaryInf_Vsb : IsUnitaryInf Vsb := by
  intro κ _ _ A hA
  obtain ⟨U, hU⟩ := isPureInf_Vsb κ A hA
  have he : (fun r c => U (lp.single 2 c (1 : ℂ)) r) = composeOp Vsb A := by
    funext r c; exact hU r c
  have hrow : IsCoIsoKernel (fun r c => U (lp.single 2 c (1 : ℂ)) r) := by
    rw [he]
    exact isCoIsoKernel_compose_Vsb _ fun k => isCoIsoKernel_entOp (A k) (hA k)
  exact ⟨LinearIsometryEquiv.ofSurjective U (surjective_of_isCoIsoKernel U hrow), hU⟩

/-- Purifiability by a process that is unitary against countable ancillas. -/
def PurifiableUnitaryInf (p : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∃ (V : Proc (Fin 8 × Fin 8) (Fin 8 × Fin 8)) (ψ : Fin 8 × Fin 8 → ℂ),
    (∑ π, ‖ψ π‖ ^ 2) = 1 ∧ IsUnitaryInf V ∧ IsPure V ∧ p = inducedP V ψ

/-- **Theorem H.12.1, unitary form with countable ancillas.** -/
theorem purification_conjecture_false_unitaryInf :
    ∃ p : Fin 8 → Fin 8 → ℝ, Valid p ∧ PurifiableUnitaryInf p ∧
      p ∉ convexHull ℝ {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
        (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} := by
  have hset : {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} = PFset := by
    ext x; simp only [PFset, Set.mem_ofPred_eq, isPF_iff]
  have h3 := pcl_not_mem_convexHull
  rw [← hset] at h3
  exact ⟨pcl, valid_pcl,
    ⟨Vsb, psiSrc, norm_psiSrc, isUnitaryInf_Vsb, isPure_Vsb, inducedP_Vsb⟩, h3⟩

end PFUL.Counterexample
