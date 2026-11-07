import PFUL.CountablePerturbation

open Set Filter Topology
namespace PFUL.Infinite

/-- No exceptional set or regularity hypothesis is needed if every point in the
closure of the output range differs finitely from one fixed baseline. -/
theorem exists_fixed_of_rangeClosure_finite_diff
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F) (c : ℕ → Bool)
    (hcl : ∀ y ∈ closure (Set.range F), {k | y k ≠ c k}.Finite) :
    ∃ x, F x = x := by
  choose x hx hxF using exists_prefix_fixed hex c
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := x) fun _ => mem_univ _
  have houtlim : Tendsto (fun m => F (x (φ m))) atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr
    intro k
    exact (((continuous_apply k).tendsto y).comp hlim).congr'
      ((hφ.tendsto_atTop.eventually_gt_atTop k).mono fun m hm => (hxF (φ m) k hm).symm)
  have hy : y ∈ closure (Set.range F) := mem_closure_of_tendsto houtlim
    (Eventually.of_forall fun m => mem_range_self (x (φ m)))
  have hyc := hcl y hy
  have hyout := hcl (F y) (subset_closure (mem_range_self y))
  have hyF : {k | F y k ≠ y k}.Finite :=
    (hyout.union hyc).subset fun k hk => by
      by_contra h
      simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
      exact hk (by rw [h.1, h.2])
  obtain ⟨N1, hN1⟩ := hyc.bddAbove
  obtain ⟨N2, hN2⟩ := hyF.bddAbove
  let N := N1 + N2 + 1
  have hag : ∀ k ∈ Finset.range N, ∀ᶠ m in atTop, x (φ m) k = y k := fun k _ =>
    eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto y).comp hlim)
  obtain ⟨m, hm1, hm2⟩ := (((Filter.eventually_all_finset _).mpr hag).and
    (hφ.tendsto_atTop.eventually_ge_atTop N)).exists
  refine ⟨y, fixed_of_prefix_agree hex c hx hxF (N := N) (fun k hk => ?_) (fun k hk => ?_)
    hm2 (fun k hk => hm1 k (Finset.mem_range.mpr hk))⟩
  · by_contra h
    have := hN1 h
    dsimp [N] at hk
    omega
  · by_contra h
    have := hN2 h
    dsimp [N] at hk
    omega

/-- Uniformly bounded output weight relative to any baseline forces a fixed point.
This concerns outputs, not exceptional inputs, and needs no Baire assumption. -/
theorem exists_fixed_of_bounded_output_diff
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F) (c : ℕ → Bool) (K : ℕ)
    (hbd : ∀ x (T : Finset ℕ), (∀ k ∈ T, F x k ≠ c k) → T.card ≤ K) :
    ∃ x, F x = x := by
  classical
  let B : Set (ℕ → Bool) := ⋂ T : Finset ℕ, {s | (∀ k ∈ T, s k ≠ c k) → T.card ≤ K}
  have hB : IsClosed B := isClosed_iInter fun T => by
    have : Continuous fun s : ℕ → Bool => decide ((∀ k ∈ T, s k ≠ c k) → T.card ≤ K) :=
      continuous_of_finset_dep T fun x y hxy => by
        simp only [decide_eq_decide]
        exact imp_congr_left (forall₂_congr fun k hk => by rw [hxy k hk])
    have h := (isClosed_discrete {true}).preimage this
    convert h using 1
    ext s
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, decide_eq_true_eq]
  apply exists_fixed_of_rangeClosure_finite_diff hex c
  intro y hy
  have hyB : y ∈ B := (closure_minimal (by
    rintro _ ⟨x, rfl⟩
    exact mem_iInter.mpr fun T => hbd x T) hB) hy
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (K + 1)
  have := mem_iInter.mp hyB T (fun k hk => hT hk)
  omega

/-- In particular, a closed output range contained in one finite-difference class
suffices, regardless of the cardinality or structure of the exceptional inputs. -/
theorem exists_fixed_of_closed_range_finite_diff
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F) (c : ℕ → Bool)
    (hc : IsClosed (Set.range F)) (hfin : ∀ x, {k | F x k ≠ c k}.Finite) :
    ∃ x, F x = x := by
  apply exists_fixed_of_rangeClosure_finite_diff hex c
  intro y hy
  rw [hc.closure_eq] at hy
  obtain ⟨x, rfl⟩ := hy
  exact hfin x

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_fixed_of_rangeClosure_finite_diff
#print axioms PFUL.Infinite.exists_fixed_of_bounded_output_diff
#print axioms PFUL.Infinite.exists_fixed_of_closed_range_finite_diff
