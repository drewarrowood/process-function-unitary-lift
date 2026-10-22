import PFUL.TraceClass

/-!
# Completely positive trace-preserving maps on trace-class operators

`IsCPTP Φ` for a map `Φ` from operators on `H` to operators on `K` (only its values on the trace
class matter): `Φ` maps the trace class into the trace class, is linear there, preserves the trace,
and is completely positive, i.e. `Φ ⊗ id_Z` preserves positivity of trace-class operators on
`ℓ²(Z; H) ≅ H ⊗ ℂ^Z` for every finite ancilla `Z` (`ampMap`).

`isCPTP_stinespring`: every Stinespring channel `ρ ↦ Tr_J(V ρ V†)`, with `V : H → ℓ²(J; K)` an
isometry and `J` an arbitrary (e.g. countable) Kraus index, is CPTP. With Kraus operators
`K_j = slot_j† V` this is `ρ ↦ ∑_j K_j ρ K_j†`, `∑_j K_j† K_j = V†V = 1`: **Kraus ⇒ CPTP**.
-/

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap

set_option linter.unusedSectionVars false

universe u

namespace PFUL.TraceClass

variable {H H' : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- The trace class is stable under `T ↦ A T B` for bounded `A : H → H'`, `B : H' → H`. -/
theorem sandwich_mem (A : H →L[ℂ] H') (B : H' →L[ℂ] H) {T : H →L[ℂ] H}
    (hT : T ∈ traceClass H) : A ∘L T ∘L B ∈ traceClass H' := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨K, _, _, _, A', B', hA, hB, rfl⟩ := hT
    have : A ∘L (adjoint A' ∘L B') ∘L B = adjoint (A' ∘L adjoint A) ∘L (B' ∘L B) := by
      rw [adjoint_comp, adjoint_adjoint]; simp only [comp_assoc]
    rw [this]; exact adjoint_comp_mem (hA.comp_right _) (hB.comp_right _)
  | zero => simp
  | add x y _ _ hx hy => rw [add_comp, comp_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comp, comp_smul]; exact Submodule.smul_mem _ a hx

theorem isPositive_of_inner_nonneg {T : H →L[ℂ] H} (h : ∀ x, 0 ≤ ⟪x, T x⟫_ℂ) : T.IsPositive := by
  rw [isPositive_iff_complex]
  intro x
  have hz : 0 ≤ ⟪T x, x⟫_ℂ := by rw [← inner_conj_symm]; exact star_nonneg_iff.2 (h x)
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hz
  exact ⟨Complex.ext (by simp) (by simpa using h2), h1⟩

section Amp
variable {Z : Type u} [DecidableEq Z]

theorem adjoint_slot_apply (z : Z) (f : lp (fun _ : Z => H) 2) : adjoint (slot z) f = f z :=
  ext_inner_right ℂ fun x => by rw [adjoint_inner_left, inner_slot_right]

variable [Fintype Z]
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Block amplification `Φ ⊗ id_Z`: `(Φ ⊗ id)(T)_{z z'} = Φ(T_{z z'})`. -/
noncomputable def ampMap (Z : Type u) [DecidableEq Z] [Fintype Z]
    (Φ : (H →L[ℂ] H) → (K →L[ℂ] K))
    (T : lp (fun _ : Z => H) 2 →L[ℂ] lp (fun _ : Z => H) 2) :
    lp (fun _ : Z => K) 2 →L[ℂ] lp (fun _ : Z => K) 2 :=
  ∑ z, ∑ z', slot z ∘L Φ (adjoint (slot z) ∘L T ∘L slot z') ∘L adjoint (slot z')

theorem inner_ampMap (Φ : (H →L[ℂ] H) → (K →L[ℂ] K))
    (T : lp (fun _ : Z => H) 2 →L[ℂ] lp (fun _ : Z => H) 2) (x : lp (fun _ : Z => K) 2) :
    ⟪x, ampMap Z Φ T x⟫_ℂ =
      ∑ z, ∑ z', ⟪x z, Φ (adjoint (slot z) ∘L T ∘L slot z') (x z')⟫_ℂ := by
  simp only [ampMap, sum_apply, inner_sum, comp_apply, inner_slot_right, adjoint_slot_apply]

end Amp

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Completely positive, trace-preserving maps on the trace class. -/
structure IsCPTP (Φ : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop where
  mem : ∀ T ∈ traceClass H, Φ T ∈ traceClass K
  map_add : ∀ S ∈ traceClass H, ∀ T ∈ traceClass H, Φ (S + T) = Φ S + Φ T
  map_smul : ∀ (a : ℂ), ∀ T ∈ traceClass H, Φ (a • T) = a • Φ T
  trace_eq : ∀ T ∈ traceClass H, trace (Φ T) = trace T
  cp : ∀ (Z : Type u) [DecidableEq Z] [Fintype Z]
    (T : lp (fun _ : Z => H) 2 →L[ℂ] lp (fun _ : Z => H) 2),
    T ∈ traceClass _ → T.IsPositive → (ampMap Z Φ T).IsPositive

/-- `Φ ⊗ id` with a one-point ancilla is `Φ` up to `ℓ²(Unit; ·) ≅ ·`; positivity on `H` itself. -/
theorem IsCPTP.isPositive {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsCPTP Φ) {T : H →L[ℂ] H}
    (hT : T ∈ traceClass H) (hpos : T.IsPositive) : (Φ T).IsPositive := by
  refine isPositive_of_inner_nonneg fun x => ?_
  have hs : adjoint (slot PUnit.unit) ∘L (slot PUnit.unit : H →L[ℂ] lp (fun _ : PUnit.{u+1} => H) 2)
      = ContinuousLinearMap.id ℂ H := by
    ext y; simp [adjoint_slot_apply, slot_apply]
  have e : adjoint (slot PUnit.unit) ∘L ((slot PUnit.unit : H →L[ℂ] lp (fun _ : PUnit.{u+1} => H) 2)
      ∘L T ∘L adjoint (slot PUnit.unit)) ∘L slot PUnit.unit = T := by
    simp only [← comp_assoc]; rw [hs, id_comp, comp_assoc, hs, comp_id]
  have hpos' := h.cp PUnit _ (conj_mem (slot PUnit.unit) hT) (hpos.conj_adjoint (slot PUnit.unit))
  have := hpos'.inner_nonneg_right (slot PUnit.unit x)
  rw [inner_ampMap] at this
  simp only [Finset.univ_unique, Finset.sum_singleton, e] at this
  simpa [slot_apply] using this

theorem IsCPTP.isDensity {Φ : (H →L[ℂ] H) → (K →L[ℂ] K)} (h : IsCPTP Φ) {ρ : H →L[ℂ] H}
    (hρ : IsDensity ρ) : IsDensity (Φ ρ) :=
  ⟨h.mem ρ hρ.1, h.isPositive hρ.1 hρ.2.1, by rw [h.trace_eq ρ hρ.1, hρ.2.2]⟩

section Stinespring
variable {J : Type u} [DecidableEq J]

/-- The Stinespring channel `ρ ↦ Tr_J (V ρ V†)`. -/
noncomputable def stinespring (V : H →L[ℂ] lp (fun _ : J => K) 2) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  ptrace (V ∘L T ∘L adjoint V)

/-- **Kraus/Stinespring ⇒ CPTP.** -/
theorem isCPTP_stinespring (V : H →L[ℂ] lp (fun _ : J => K) 2)
    (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ H) : IsCPTP (stinespring V) where
  mem T hT := ptrace_mem (conj_mem V hT)
  map_add S hS T hT := by
    simp only [stinespring, add_comp, comp_add]
    exact ptrace_add (conj_mem V hS) (conj_mem V hT)
  map_smul a T hT := by
    simp only [stinespring, smul_comp, comp_smul]
    exact ptrace_smul a (conj_mem V hT)
  trace_eq T hT := by
    rw [stinespring, trace_ptrace (conj_mem V hT), trace_conj V hV hT]
  cp Z _ _ T hT hpos := by
    refine isPositive_of_inner_nonneg fun x => ?_
    rw [inner_ampMap]
    have hmem : ∀ z z', V ∘L (adjoint (slot z) ∘L T ∘L slot z') ∘L adjoint V ∈
        traceClass (lp (fun _ : J => K) 2) :=
      fun z z' => sandwich_mem V (adjoint V)
        (sandwich_mem (H := lp (fun _ : Z => H) 2) (H' := H) (adjoint (slot z)) (slot z') hT)
    let w : J → lp (fun _ : Z => H) 2 := fun j => ∑ z, slot z (adjoint V (slot j (x z)))
    have hterm : ∀ j, ⟪w j, T (w j)⟫_ℂ = ∑ z, ∑ z',
        ⟪slot j (x z), (V ∘L (adjoint (slot z) ∘L T ∘L slot z') ∘L adjoint V)
          (slot j (x z'))⟫_ℂ := by
      intro j
      simp only [w, map_sum, sum_inner, inner_sum, comp_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
      conv_rhs => rw [← adjoint_inner_left, adjoint_inner_right]
    have hsum : HasSum (fun j => ⟪w j, T (w j)⟫_ℂ)
        (∑ z, ∑ z', ⟪x z, stinespring V (adjoint (slot z) ∘L T ∘L slot z') (x z')⟫_ℂ) := by
      simp_rw [hterm]
      exact hasSum_sum fun z _ => hasSum_sum fun z' _ =>
        hasSum_inner_ptrace (hmem z z') (x z) (x z')
    exact hsum.nonneg fun j => hpos.inner_nonneg_right _

end Stinespring

end PFUL.TraceClass
