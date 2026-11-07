import PFUL.BaireClasses

open Set Filter Topology
namespace PFUL.Infinite

/-- Reverse-triangular finite processes, with constant true output above the cutoff. -/
noncomputable def finiteYablo (N : ℕ) (s : ℕ → Bool) (k : ℕ) : Bool :=
  decide (∀ j ∈ Finset.Ioo k N, s j = false)

theorem finiteYablo_continuous (N : ℕ) : Continuous (finiteYablo N) := by
  classical
  apply continuous_pi
  intro k
  apply continuous_of_finset_dep (Finset.Ioo k N)
  intro x y hxy
  simp only [finiteYablo, decide_eq_decide]
  exact forall₂_congr fun j hj => by rw [hxy j hj]

/-- Each approximant is globally exclusive, not merely exclusive on finite faces. -/
theorem finiteYablo_exclusive (N : ℕ) : Exclusive (finiteYablo N) := by
  classical
  intro s t hst
  by_cases hout : ∃ k, N ≤ k ∧ s k ≠ t k
  · obtain ⟨k, hkN, hk⟩ := hout
    refine ⟨k, hk, ?_⟩
    have he : Finset.Ioo k N = ∅ := Finset.Ioo_eq_empty_of_le (by omega)
    simp [finiteYablo, he]
  · have htail : ∀ k, N ≤ k → s k = t k := by
      intro k hk
      by_contra h
      exact hout ⟨k, hk, h⟩
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hst
    have hrN : r < N := by
      by_contra h
      exact hr (htail r (by omega))
    let D := (Finset.range N).filter (fun k => s k ≠ t k)
    have hD : D.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrN, hr⟩⟩
    let k := D.max' hD
    have hkD : k ∈ D := Finset.max'_mem D hD
    have hk : s k ≠ t k := (Finset.mem_filter.mp hkD).2
    have heq : ∀ j ∈ Finset.Ioo k N, s j = t j := by
      intro j hj
      by_contra h
      have hjD : j ∈ D := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Finset.mem_Ioo.mp hj).2, h⟩
      have hle : j ≤ k := Finset.le_max' D j hjD
      have hgt : k < j := (Finset.mem_Ioo.mp hj).1
      omega
    refine ⟨k, hk, ?_⟩
    simp only [finiteYablo, decide_eq_decide]
    exact forall₂_congr fun j hj => by rw [heq j hj]

theorem finiteYablo_limit (s : ℕ → Bool) :
    Tendsto (fun N => finiteYablo N s) atTop (𝓝 (yablo s)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_bool_of_eventually
  by_cases hs : ∀ j, k < j → s j = false
  · exact Eventually.of_forall fun N => by
      simp only [finiteYablo, yablo, decide_eq_decide]
      exact ⟨fun _ j hj => hs j hj, fun _ j hj => hs j (Finset.mem_Ioo.mp hj).1⟩
  · push Not at hs
    obtain ⟨j, hj, hsj⟩ := hs
    filter_upwards [eventually_gt_atTop j] with N hN
    simp only [finiteYablo, yablo, decide_eq_decide]
    constructor
    · intro h
      exact (hsj (h j (Finset.mem_Ioo.mpr ⟨hj, hN⟩))).elim
    · intro h
      exact (hsj (h j hj)).elim

/-- Global exclusivity is not closed under pointwise convergence, even for a
sequence of continuous exclusive maps with a genuine Baire-one limit. This is
NOT a Baire-one exclusive counterexample: the limit fails global exclusivity. -/
theorem continuous_exclusive_limit_can_fail_exclusive :
    (∀ N, Continuous (finiteYablo N) ∧ Exclusive (finiteYablo N)) ∧
    (∀ s, Tendsto (fun N => finiteYablo N s) atTop (𝓝 (yablo s))) ∧
    BaireOne yablo ∧ (∀ s, yablo s ≠ s) ∧ ¬ Exclusive yablo :=
  ⟨fun N => ⟨finiteYablo_continuous N, finiteYablo_exclusive N⟩,
    finiteYablo_limit, yablo_baireOne, yablo_ne, yablo_not_exclusive⟩

/-- Finite-difference pairwise exclusivity DOES survive pointwise limits. The
failure above is necessarily at a pair with infinitely many differing bits. -/
theorem finite_pair_exclusive_of_pointwise_limit
    {G : ℕ → (ℕ → Bool) → (ℕ → Bool)} {F : (ℕ → Bool) → (ℕ → Bool)}
    (hG : ∀ n, Exclusive (G n))
    (hlim : ∀ s, Tendsto (fun n => G n s) atTop (𝓝 (F s)))
    {s t : ℕ → Bool} (hst : s ≠ t) (hfin : {k | s k ≠ t k}.Finite) :
    ∃ k, s k ≠ t k ∧ F s k = F t k := by
  have hev : ∀ k ∈ hfin.toFinset, ∀ᶠ n in atTop,
      G n s k = F s k ∧ G n t k = F t k := fun k _ =>
    (eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto (F s)).comp (hlim s))).and
      (eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto (F t)).comp (hlim t)))
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset _).mpr hev).exists
  obtain ⟨k, hk, hw⟩ := hG n s t hst
  have hh := hn k (hfin.mem_toFinset.mpr hk)
  exact ⟨k, hk, hh.1.symm.trans (hw.trans hh.2)⟩

theorem yablo_finite_pair_exclusive {s t : ℕ → Bool}
    (hst : s ≠ t) (hfin : {k | s k ≠ t k}.Finite) :
    ∃ k, s k ≠ t k ∧ yablo s k = yablo t k :=
  finite_pair_exclusive_of_pointwise_limit finiteYablo_exclusive finiteYablo_limit hst hfin

end PFUL.Infinite

#print axioms PFUL.Infinite.finiteYablo_exclusive
#print axioms PFUL.Infinite.continuous_exclusive_limit_can_fail_exclusive

#print axioms PFUL.Infinite.finite_pair_exclusive_of_pointwise_limit
#print axioms PFUL.Infinite.yablo_finite_pair_exclusive
