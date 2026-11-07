import PFUL.CountablePerturbation

open Set Filter Topology
namespace PFUL.Infinite

/-- A countable set cannot contain a full coordinate box with infinitely many free bits. -/
theorem finite_diff_of_countable_box {ι : Type*} {S : Set (ι → Bool)}
    (hS : S.Countable) {y c : ι → Bool}
    (hbox : ∀ t, (∀ k, y k ≠ t k → y k ≠ c k) → t ∈ S) :
    {k | y k ≠ c k}.Finite := by
  classical
  by_contra hinf
  let Z := {k | y k ≠ c k}
  have : Infinite Z := Set.infinite_coe_iff.2 hinf
  let φ : (Z → Bool) → (ι → Bool) :=
    fun d k => if h : k ∈ Z then d ⟨k, h⟩ else y k
  have hφ : Function.Injective φ := fun d d' h => funext fun ⟨k, hk⟩ => by
    have := congrFun h k
    simpa [φ, hk] using this
  have hrange : ∀ d, φ d ∈ S := fun d => hbox (φ d) fun k hk => by
    by_contra hz
    exact hk (by simp [φ, show k ∉ Z from fun h => h hz])
  have : Countable (Z → Bool) := by
    have := hS.to_subtype
    exact Function.Injective.countable (f := fun d => (⟨φ d, hrange d⟩ : S))
      fun d d' h => hφ (congrArg Subtype.val h)
  exact not_countable_fun_bool_of_infinite Z this

/-- Prefix solutions frozen to `c` generate downward coordinate boxes inside `S`.
Every subsequential limit generates its entire downward box, provided `S` is closed. -/
theorem cluster_box_subset_of_prefix_fixed {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hc : IsClosed S)
    {x : ℕ → ℕ → Bool}
    (hxS : ∀ n, x n ∈ S)
    (hx : ∀ n k, n ≤ k → x n k = c k)
    (hxF : ∀ n k, k < n → F (x n) k = x n k)
    {φ : ℕ → ℕ} {y : ℕ → Bool}
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 y))
    (t : ℕ → Bool) (ht : ∀ k, y k ≠ t k → y k ≠ c k) : t ∈ S := by
  classical
  let mask : (ℕ → Bool) → ℕ → Bool := fun d k => if t k = c k then c k else d k
  have hmask : Continuous mask := continuous_pi fun k => by
    by_cases h : t k = c k
    · simpa [mask, h] using (continuous_const : Continuous fun _ : (ℕ → Bool) => c k)
    · simpa [mask, h] using (continuous_apply k : Continuous fun d : (ℕ → Bool) => d k)
  have hmy : mask y = t := funext fun k => by
    have h := ht k
    cases hy : y k <;> cases ht' : t k <;> cases hc' : c k <;>
      simp_all [mask]
  have hmS : ∀ n, mask (x n) ∈ S := fun n => box_subset hex hF (hxS n) _ fun k hk => by
    have hxc : x n k ≠ c k := by
      intro heq
      apply hk
      simp [mask, heq]
    have hkn : k < n := by
      by_contra h
      exact hxc (hx n k (by omega))
    rw [hxF n k hkn]
    exact hxc
  have hlimit : Tendsto (fun m => mask (x (φ m))) atTop (𝓝 t) := by
    simpa only [hmy, Function.comp_def] using (hmask.tendsto y).comp hlim
  exact hc.mem_of_tendsto hlimit (Eventually.of_forall fun m => hmS (φ m))

/-- **Countable-closed perturbation theorem.** An exclusive Boolean map that equals a
constant away from a countable closed subset of Cantor space has a fixed point. -/
theorem exists_fixed_of_const_off_countable_closed {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hc : IsClosed S) :
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
  have hyc : {k | y k ≠ c k}.Finite := finite_diff_of_countable_box hS hybox
  have hyS : y ∈ S := hybox y fun _ h => (h rfl).elim
  have hyF : {k | F y k ≠ y k}.Finite :=
    ((finite_defect_of_countable hex hF hS hyS).union hyc).subset fun k hk => by
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

/-- The fixed point is unique, by exclusivity. -/
theorem exists_unique_fixed_of_const_off_countable_closed {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hc : IsClosed S) :
    ∃! x, F x = x := by
  obtain ⟨x, hx⟩ := exists_fixed_of_const_off_countable_closed hex hF hS hc
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  obtain ⟨k, hk, hw⟩ := hex y x hne
  rw [hy, hx] at hw
  exact hk hw

/-- The unique solution differs from the off-set constant in only finitely many bits. -/
theorem fixed_finite_diff_of_const_off_countable {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c x : ℕ → Bool}
    (hF : ∀ z, z ∉ S → F z = c) (hS : S.Countable) (hx : F x = x) :
    {k | x k ≠ c k}.Finite := by
  by_cases h : x ∈ S
  · simpa only [hx] using finite_defect_of_countable hex hF hS h
  · have heq : x = c := hx.symm.trans (hF x h)
    simp [heq]

end PFUL.Infinite

#print axioms PFUL.Infinite.finite_diff_of_countable_box
#print axioms PFUL.Infinite.cluster_box_subset_of_prefix_fixed
#print axioms PFUL.Infinite.exists_fixed_of_const_off_countable_closed

#print axioms PFUL.Infinite.exists_unique_fixed_of_const_off_countable_closed
#print axioms PFUL.Infinite.fixed_finite_diff_of_const_off_countable
