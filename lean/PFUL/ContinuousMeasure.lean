/-
F.5.3 (Lean): for a measurable process function `w` on a finite product of standard Borel
abelian groups, each carrying a σ-finite right-invariant measure (Haar/volume, counting
measure, ...), the closed-loop translation map `tau w o = o - w o` preserves the product
measure.  Proof: induction on the number of parties, splitting off one party `a`, a skew
product (induction hypothesis on the reduced process) followed by a shear `x ↦ x - c e'`
whose offset is independent of `x` by `fiber_const`; measurability of the inverse comes from
Lusin–Souslin (`Measurable.measurableEmbedding`).
-/
import PFUL.Continuous
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option linter.unusedSectionVars false

namespace PFUL.Continuous

open MeasureTheory

section meas
variable {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ k, AddCommGroup (G k)]
  [∀ k, MeasurableSpace (G k)] [∀ k, MeasurableSub₂ (G k)]

theorem tau_measurable {w : (∀ k, G k) → (∀ k, G k)} (hwm : Measurable w) :
    Measurable (tau w) := by
  refine measurable_pi_iff.mpr fun k => ?_
  exact (measurable_pi_apply k).sub ((measurable_pi_apply k).comp hwm)

theorem tauInv_measurable [Countable ι] [∀ k, StandardBorelSpace (G k)]
    {w : (∀ k, G k) → (∀ k, G k)} (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) :
    Measurable (tauInv hw) := by
  have hE : MeasurableEmbedding (tau w) :=
    (tau_measurable hwm).measurableEmbedding (tau_bijective hw).1
  intro s hs
  have : tauInv hw ⁻¹' s = tau w '' s := by
    ext e; constructor
    · intro h; exact ⟨_, h, tau_tauInv hw e⟩
    · rintro ⟨o, ho, rfl⟩
      show tauInv hw (tau w o) ∈ s
      rwa [(tau_bijective hw).1 (tau_tauInv hw (tau w o))]
  rw [this]; exact hE.measurableSet_image.2 hs
end meas

theorem tau_measurePreserving_aux : ∀ (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (_ : Fintype.card ι = n) {G : ι → Type} [∀ k, AddCommGroup (G k)]
    [∀ k, MeasurableSpace (G k)] [∀ k, MeasurableAdd (G k)] [∀ k, MeasurableSub₂ (G k)]
    [∀ k, StandardBorelSpace (G k)] (μ : ∀ k, Measure (G k)) [∀ k, SigmaFinite (μ k)]
    [∀ k, (μ k).IsAddRightInvariant] (w : (∀ k, G k) → (∀ k, G k)) (_ : Measurable w)
    (_ : PFUL.Countable.IsProcessFunction (I := G) (O := G) w),
    MeasurePreserving (tau w) (Measure.pi μ) (Measure.pi μ) := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hc G _ _ _ _ _ μ _ _ w _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    have : tau w = id := by funext o k; exact (IsEmpty.false k).elim
    rw [this]; exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hc G _ _ _ _ _ μ _ _ w hwm hw
    obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let p : ι → Prop := fun i => i ≠ a
    let E := MeasurableEquiv.piEquivPiSubtypeProd G p
    let μR := Measure.pi fun i : {i // p i} => μ i
    let μA := Measure.pi fun i : {i // ¬ p i} => μ i
    have hE : MeasurePreserving E (Measure.pi μ) (μR.prod μA) :=
      measurePreserving_piEquivPiSubtypeProd μ p
    let E2 := E.trans MeasurableEquiv.prodComm
    have hE2 : MeasurePreserving E2 (Measure.pi μ) (μA.prod μR) :=
      (Measure.measurePreserving_swap).comp hE
    have hEs1 : ∀ r x (i : {i // p i}), E.symm (r, x) i.1 = r i := by
      intro r x i; show (if h : p i.1 then r ⟨i.1, h⟩ else x ⟨i.1, h⟩) = r i
      simp only [i.2, ↓reduceDIte]
    have hEs2 : ∀ r x (i : {i // ¬ p i}), E.symm (r, x) i.1 = x i := by
      intro r x i; show (if h : p i.1 then r ⟨i.1, h⟩ else x ⟨i.1, h⟩) = x i
      simp only [i.2, ↓reduceDIte]
    -- reduced process
    let wx : (∀ i : {i // ¬ p i}, G i) → (∀ i : {i // p i}, G i) → (∀ i : {i // p i}, G i) :=
      fun x r i => w (E.symm (r, x)) i
    have hwx : ∀ x, PFUL.Countable.IsProcessFunction (I := fun i : {i // p i} => G i)
        (O := fun i : {i // p i} => G i) (wx x) := by
      intro x f'
      let f : ∀ k, G k → G k := fun k y => if h : p k then f' ⟨k, h⟩ y else x ⟨k, h⟩
      obtain ⟨s, hs, hu⟩ := hw f
      have hsx : E.symm (fun i => s i, x) = s := by
        funext k
        by_cases h : p k
        · exact hEs1 _ _ ⟨k, h⟩
        · rw [hEs2 _ _ ⟨k, h⟩, ← hs k]; show _ = (if h : p k then _ else _); simp only [h, ↓reduceDIte]
      refine ⟨fun i => s i, fun i => ?_, fun r' hr' => ?_⟩
      · show f' i (w (E.symm (fun i => s i, x)) i) = s i
        rw [hsx, ← hs i.1]; show _ = (if h : p i.1 then _ else _); simp only [i.2, ↓reduceDIte]
      · have : E.symm (r', x) = s := by
          apply hu; intro k
          by_cases h : p k
          · show (if h : p k then _ else _) = _
            simp only [h, ↓reduceDIte]; rw [hEs1 _ _ ⟨k, h⟩]; exact hr' ⟨k, h⟩
          · show (if h : p k then _ else _) = _
            simp only [h, ↓reduceDIte]; rw [hEs2 _ _ ⟨k, h⟩]
        funext i; rw [← this, hEs1]
    have hcard : Fintype.card {i // p i} = n := by
      have := Fintype.card_subtype_compl (fun i : ι => i = a)
      simp only [Fintype.card_unique] at this
      simp only [p]; rw [this]; omega
    have htx : ∀ x r, tau (wx x) r = (E (tau w (E.symm (r, x)))).1 := by
      intro x r; funext i
      show r i - w (E.symm (r, x)) i = E.symm (r, x) i.1 - w (E.symm (r, x)) i.1
      rw [hEs1]
    -- σ
    let σ : (∀ i : {i // ¬ p i}, G i) × (∀ i : {i // p i}, G i) → _ :=
      fun q => (id q.1, tau (wx q.1) q.2)
    have hσ : MeasurePreserving σ (μA.prod μR) (μA.prod μR) := by
      refine (MeasurePreserving.id μA).skew_product (g := fun x r => tau (wx x) r) ?_ ?_
      · have : (Function.uncurry fun x r => tau (wx x) r) =
            fun q : (∀ i : {i // ¬ p i}, G i) × (∀ i : {i // p i}, G i) =>
              (E (tau w (E.symm (q.2, q.1)))).1 := by
          funext q; exact htx q.1 q.2
        rw [this]
        exact measurable_fst.comp (E.measurable.comp ((tau_measurable hwm).comp
          (E.symm.measurable.comp measurable_swap)))
      · refine Filter.Eventually.of_forall fun x => ?_
        refine (ih hcard (fun i => μ i) (wx x) ?_ (hwx x)).map_eq
        exact measurable_pi_iff.mpr fun (i : {i // p i}) => (measurable_pi_apply i.1).comp
          (hwm.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const)))
    -- ρ
    let c' : (∀ i : {i // p i}, G i) → (∀ i : {i // ¬ p i}, G i) :=
      fun e' => (E (w (tauInv hw (E.symm (e', 0))))).2
    have hc' : Measurable c' := measurable_snd.comp (E.measurable.comp (hwm.comp
      ((tauInv_measurable hwm hw).comp (E.symm.measurable.comp
        (measurable_id.prodMk measurable_const)))))
    let ρ : (∀ i : {i // ¬ p i}, G i) × (∀ i : {i // p i}, G i) → _ :=
      fun q => (q.1 - c' q.2, q.2)
    have hρ : MeasurePreserving ρ (μA.prod μR) (μA.prod μR) := by
      have h1 : MeasurePreserving (fun q : (∀ i : {i // p i}, G i) × (∀ i : {i // ¬ p i}, G i) =>
          (id q.1, (fun e' x => x - c' e') q.1 q.2)) (μR.prod μA) (μR.prod μA) :=
        (MeasurePreserving.id μR).skew_product (measurable_snd.sub (hc'.comp measurable_fst))
          (Filter.Eventually.of_forall fun e' => (measurePreserving_sub_right μA (c' e')).map_eq)
      have := (Measure.measurePreserving_swap.comp h1).comp (Measure.measurePreserving_swap (μ := μA) (ν := μR))
      convert this using 1
      funext q; rfl
    -- key identity
    have key : ∀ q, E2 (tau w (E2.symm q)) = ρ (σ q) := by
      rintro ⟨x, r⟩
      set o := E.symm (r, x) with ho
      have hE2s : E2.symm (x, r) = o := rfl
      rw [hE2s]
      have hσq : σ (x, r) = (x, (E (tau w o)).1) := by
        show (x, tau (wx x) r) = _; rw [htx]
      rw [hσq]
      show ((E (tau w o)).2, (E (tau w o)).1) = (x - c' (E (tau w o)).1, (E (tau w o)).1)
      congr 1
      funext i
      obtain ⟨j, hj⟩ := i
      have hja : j = a := not_not.mp hj
      subst hja
      show o j - w o j = x ⟨j, hj⟩ - w (tauInv hw (E.symm ((E (tau w o)).1, 0))) j
      rw [ho, hEs2 r x ⟨j, hj⟩]
      congr 1
      apply fiber_const hw j
      intro k hk
      rw [tau_tauInv, hEs1 _ _ ⟨k, hk⟩]
      rfl
    have hfun : tau w = E2.symm ∘ (ρ ∘ σ) ∘ E2 := by
      funext o
      apply E2.injective
      simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
      rw [← key, MeasurableEquiv.symm_apply_apply]
    rw [hfun]
    exact (hE2.symm E2).comp ((hρ.comp hσ).comp hE2)

/-- **F.5.3 (Lean).** For a measurable process function on a finite product of standard
Borel abelian groups with σ-finite right-invariant measures (Haar, Lebesgue volume on `ℝⁿ`,
the circle, counting measure on a countable group, …), the closed-loop translation map
`o ↦ o - w o` is measure preserving for the product measure. -/
theorem tau_measurePreserving {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ k, AddCommGroup (G k)] [∀ k, MeasurableSpace (G k)] [∀ k, MeasurableAdd (G k)]
    [∀ k, MeasurableSub₂ (G k)] [∀ k, StandardBorelSpace (G k)] (μ : ∀ k, Measure (G k))
    [∀ k, SigmaFinite (μ k)] [∀ k, (μ k).IsAddRightInvariant]
    {w : (∀ k, G k) → (∀ k, G k)} (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := G) (O := G) w) :
    MeasurePreserving (tau w) (Measure.pi μ) (Measure.pi μ) :=
  tau_measurePreserving_aux _ rfl μ w hwm hw

end PFUL.Continuous

namespace PFUL.Continuous
open MeasureTheory

/-- F.5.3 for real alphabets `ℝ` with Lebesgue measure (the `ℝⁿ` case, one coordinate per party). -/
theorem tau_measurePreserving_real {ι : Type} [Fintype ι] [DecidableEq ι]
    {w : (ι → ℝ) → (ι → ℝ)} (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := fun _ : ι => ℝ) (O := fun _ => ℝ) w) :
    MeasurePreserving (tau w) volume volume := by
  exact tau_measurePreserving (fun _ => volume) hwm hw

/-- F.5.3 for circle alphabets `ℝ/Tℤ` with Haar (normalised Lebesgue) measure. -/
theorem tau_measurePreserving_circle {ι : Type} [Fintype ι] [DecidableEq ι] (T : ℝ) [Fact (0 < T)]
    {w : (ι → AddCircle T) → (ι → AddCircle T)} (hwm : Measurable w)
    (hw : PFUL.Countable.IsProcessFunction (I := fun _ : ι => AddCircle T) (O := fun _ => AddCircle T) w) :
    MeasurePreserving (tau w) (Measure.pi fun _ => volume) (Measure.pi fun _ => volume) :=
  tau_measurePreserving (fun _ => volume) hwm hw

end PFUL.Continuous
