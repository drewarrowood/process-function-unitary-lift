import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Countable alphabets: the column identity (Appendix F.3)

Finitely many parties, arbitrary input alphabets `I k`, countable output alphabets `O k` (and countable
sink ancillas `Y k`). Each local stochastic intervention `q k i` is a probability vector in `ℝ≥0∞`
(`∑' = 1`). For a process function `w`, `∑' s, ∏ k, q k (w s k) (s k) = 1`.

Proof: put the product measure (`Measure.infinitePi`) of the PMFs `q k i` on the space of all
deterministic interventions `g : (Σ k, I k) → O`; the cylinder events "`s` is a fixed point of `g`"
partition the space (unique fixed point), and each has probability `∏ k, q k (w s k) (s k)`.
-/

open MeasureTheory ENNReal

namespace PFUL.Countable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O : ι → Type*}

/-- Process function on arbitrary alphabets: every deterministic intervention has a unique fixed point. -/
def IsProcessFunction (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ f : ∀ k, I k → O k, ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k

/-- Generalised column identity, with a sink-side label `Y k` recorded together with each output:
each `p k i` is a probability vector on `O k × Y k`. -/
theorem tsum_prod_eq_one_anc {Y : ι → Type*} [∀ k, Countable (O k)] [∀ k, Countable (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (p : ∀ k, I k → O k × Y k → ℝ≥0∞) (hp : ∀ k i, ∑' z, p k i z = 1) :
    ∑' r : (∀ k, O k) × (∀ k, Y k), ∏ k, p k (w r.1 k) (r.1 k, r.2 k) = 1 := by
  classical
  let Z : (Σ k, I k) → Type _ := fun a => O a.1 × Y a.1
  letI mZ : ∀ a, MeasurableSpace (Z a) := fun _ => ⊤
  let P : ∀ a : (Σ k, I k), PMF (Z a) := fun a =>
    ⟨p a.1 a.2, by rw [← hp a.1 a.2]; exact ENNReal.summable.hasSum⟩
  let μ : ∀ a, Measure (Z a) := fun a => (P a).toMeasure
  haveI : ∀ a, IsProbabilityMeasure (μ a) := fun a => PMF.toMeasure.isProbabilityMeasure _
  let ν := Measure.infinitePi μ
  let idx : (∀ k, O k) → Finset (Σ k, I k) := fun s => Finset.univ.image (fun k => ⟨k, w s k⟩)
  let E : (∀ k, O k) × (∀ k, Y k) → Set (∀ a, Z a) := fun r =>
    Set.pi (idx r.1) (fun a => {((r.1 a.1, r.2 a.1) : Z a)})
  have hmem : ∀ r g, g ∈ E r ↔ ∀ k, g ⟨k, w r.1 k⟩ = (r.1 k, r.2 k) := by
    intro r g
    simp only [E, idx, Set.mem_pi, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h k; exact h _ ⟨k, rfl⟩
    · rintro h _ ⟨k, rfl⟩; exact h k
  have hmeas : ∀ r, MeasurableSet (E r) := fun r =>
    MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => MeasurableSpace.measurableSet_top)
  have hval : ∀ r, ν (E r) = ∏ k, p k (w r.1 k) (r.1 k, r.2 k) := by
    intro r
    rw [Measure.infinitePi_pi μ (fun _ _ => MeasurableSpace.measurableSet_top)]
    rw [Finset.prod_image (fun k _ k' _ h => (Sigma.mk.inj h).1)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSpace.measurableSet_top]
    rfl
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro r r' hne
    refine Set.disjoint_left.2 (fun g hg hg' => hne ?_)
    rw [hmem] at hg hg'
    let f : ∀ k, I k → O k := fun k i => (g ⟨k, i⟩).1
    have h1 : r.1 = r'.1 := (hw f).unique (fun k => by simp [f, hg k]) (fun k => by simp [f, hg' k])
    have h2 : r.2 = r'.2 := by
      funext k
      have a := congrArg Prod.snd (hg k)
      have b := congrArg Prod.snd (hg' k)
      rw [h1] at a
      simp only at a b
      rw [← a, ← b]
    exact Prod.ext h1 h2
  have hcover : (⋃ r, E r) = Set.univ := by
    refine Set.eq_univ_of_forall (fun g => ?_)
    let f : ∀ k, I k → O k := fun k i => (g ⟨k, i⟩).1
    obtain ⟨s, hs, -⟩ := hw f
    refine Set.mem_iUnion.2 ⟨(s, fun k => (g ⟨k, w s k⟩).2), (hmem _ _).2 (fun k => ?_)⟩
    exact Prod.ext (hs k) rfl
  calc ∑' r : (∀ k, O k) × (∀ k, Y k), ∏ k, p k (w r.1 k) (r.1 k, r.2 k)
      = ∑' r, ν (E r) := by simp_rw [hval]
    _ = ν (⋃ r, E r) := (measure_iUnion hdisj hmeas).symm
    _ = 1 := by rw [hcover, measure_univ]

/-- **Column identity on countable output alphabets** (inputs arbitrary). -/
theorem tsum_prod_eq_one [∀ k, Countable (O k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (q : ∀ k, I k → O k → ℝ≥0∞) (hq : ∀ k i, ∑' o, q k i o = 1) :
    ∑' s : (∀ k, O k), ∏ k, q k (w s k) (s k) = 1 := by
  have h := tsum_prod_eq_one_anc (Y := fun _ => PUnit.{1}) w hw (fun k i z => q k i z.1)
    (fun k i => by rw [← hq k i]; exact (Equiv.prodPUnit (O k)).tsum_eq (q k i))
  rw [← h]
  exact ((Equiv.prodUnique (∀ k, O k) (∀ k, PUnit)).tsum_eq
    (fun s => ∏ k, q k (w s k) (s k))).symm

/-- **Unit columns of the induced map, countable alphabets.** Local maps `V k` are kernels on countable
index sets whose columns have unit norm (`∑' r, ‖V k r c‖² = 1`). Then every column of the induced map
`M (f,y) (e,x) = ∏ k, V k (f k, y k) (w f k + e k, x k)` has unit norm. -/
theorem induced_colnorm {X Y : ι → Type*} [∀ k, AddCommGroup (I k)]
    [∀ k, Countable (O k)] [∀ k, Countable (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hV : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) (e : ∀ k, I k) (x : ∀ k, X k) :
    ∑' r : (∀ k, O k) × (∀ k, Y k),
      ((‖∏ k, V k (r.1 k, r.2 k) (w r.1 k + e k, x k)‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
  simp_rw [nnnorm_prod, ENNReal.ofNNReal_finsetProd, ← Finset.prod_pow]
  exact tsum_prod_eq_one_anc w hw (fun k i z => ((‖V k z (i + e k, x k)‖₊ : ℝ≥0∞)) ^ 2)
    (fun k i => hV k _)

end PFUL.Countable

#print axioms PFUL.Countable.tsum_prod_eq_one_anc
#print axioms PFUL.Countable.tsum_prod_eq_one
#print axioms PFUL.Countable.induced_colnorm
