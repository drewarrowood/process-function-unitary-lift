import PFUL.CountableClosed

open Set Filter Topology
namespace PFUL.Infinite

/-- Every full coordinate box contained in S has only finitely many free coordinates. -/
def CoordinateBoxThin (S : Set (ℕ → Bool)) : Prop :=
  ∀ (s : ℕ → Bool) (D : Set ℕ),
    (∀ t, (∀ k, s k ≠ t k → k ∈ D) → t ∈ S) → D.Finite

/-- Countability is sufficient but not necessary for coordinate-box thinness. -/
theorem coordinateBoxThin_of_countable {S : Set (ℕ → Bool)} (hS : S.Countable) :
    CoordinateBoxThin S := by
  classical
  intro s D hbox
  by_contra hD
  have : Infinite D := Set.infinite_coe_iff.mpr hD
  let embed : (D → Bool) → ℕ → Bool :=
    fun d k => if hk : k ∈ D then d ⟨k, hk⟩ else s k
  have hinj : Function.Injective embed := fun d d' h => funext fun ⟨k, hk⟩ => by
    have := congrFun h k
    simpa [embed, hk] using this
  have hmem : ∀ d, embed d ∈ S := fun d => hbox _ fun k hk => by
    by_contra hn
    exact hk (by simp [embed, hn])
  have : Countable (D → Bool) := by
    have := hS.to_subtype
    exact Function.Injective.countable (f := fun d => (⟨embed d, hmem d⟩ : S))
      fun d d' h => hinj (congrArg Subtype.val h)
  exact not_countable_fun_bool_of_infinite D this

/-- Closed exceptional sets need not be countable: exclusion of infinite coordinate
boxes suffices. This abstracts the two uses of countability in CountableClosed. -/
theorem exists_fixed_of_const_off_closed_coordinateBoxThin
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hc : IsClosed S) (hthin : CoordinateBoxThin S) :
    ∃ x, F x = x := by
  by_contra hfp
  push Not at hfp
  choose x hx hxF using exists_prefix_fixed hex c
  have hxS : ∀ n, x n ∈ S := fun n => by
    by_contra h
    have hxc : x n = c := funext fun k => by
      by_cases hk : k < n
      · rw [← hxF n k hk, hF _ h]
      · exact hx n k (by omega)
    exact hfp (x n) (by rw [hF _ h, hxc])
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := x) fun _ => mem_univ _
  have hybox : ∀ t, (∀ k, y k ≠ t k → y k ≠ c k) → t ∈ S :=
    cluster_box_subset_of_prefix_fixed hex hF hc hxS hx hxF hlim
  have hyc : {k | y k ≠ c k}.Finite := hthin y _ hybox
  have hyS : y ∈ S := hybox y fun _ h => (h rfl).elim
  have hyout : {k | F y k ≠ c k}.Finite :=
    hthin y _ (fun t ht => box_subset hex hF hyS t ht)
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
  obtain ⟨m, hm1, hm2⟩ := (((Filter.eventually_all_finset _).2 hag).and
    (hφ.tendsto_atTop.eventually_ge_atTop N)).exists
  refine hfp y (fixed_of_prefix_agree hex c hx hxF (N := N) (fun k hk => ?_) (fun k hk => ?_)
    hm2 fun k hk => hm1 k (Finset.mem_range.2 hk))
  · by_contra h
    have := hN1 h
    dsimp [N] at hk
    omega
  · by_contra h
    have := hN2 h
    dsimp [N] at hk
    omega

/-- Equivalently, any closed exceptional set supporting a fixed-point-free exclusive
map must contain a full coordinate cube with infinitely many free coordinates. -/
theorem exists_infinite_box_of_fpf_const_off_closed
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hc : IsClosed S) (hfp : ∀ x, F x ≠ x) :
    ∃ (s : ℕ → Bool) (D : Set ℕ), D.Infinite ∧
      ∀ t, (∀ k, s k ≠ t k → k ∈ D) → t ∈ S := by
  by_contra h
  push Not at h
  have hthin : CoordinateBoxThin S := by
    intro s D hbox
    by_contra hinf
    obtain ⟨t, ht, htS⟩ := h s D hinf
    exact htS (hbox t ht)
  obtain ⟨x, hx⟩ := exists_fixed_of_const_off_closed_coordinateBoxThin hex hF hc hthin
  exact hfp x hx

end PFUL.Infinite

#print axioms PFUL.Infinite.coordinateBoxThin_of_countable
#print axioms PFUL.Infinite.exists_fixed_of_const_off_closed_coordinateBoxThin
#print axioms PFUL.Infinite.exists_infinite_box_of_fpf_const_off_closed
