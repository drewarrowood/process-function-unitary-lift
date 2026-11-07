import PFUL.CountablePerturbation

open Set Filter Topology
namespace PFUL.Infinite

noncomputable def prefixNormalize (F : (ℕ → Bool) → (ℕ → Bool)) (hex : Exclusive F)
    (n : ℕ) (b : ℕ → Bool) : ℕ → Bool :=
  Classical.choose (exists_prefix_fixed hex b n)

lemma prefixNormalize_tail {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (n : ℕ) (b : ℕ → Bool) : ∀ k, n ≤ k → prefixNormalize F hex n b k = b k :=
  (Classical.choose_spec (exists_prefix_fixed hex b n)).1

lemma prefixNormalize_fixed {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (n : ℕ) (b : ℕ → Bool) : ∀ k, k < n →
      F (prefixNormalize F hex n b) k = prefixNormalize F hex n b k :=
  (Classical.choose_spec (exists_prefix_fixed hex b n)).2

/-- Finite-prefix solutions with the same boundary are unique. -/
theorem prefix_solution_unique {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (n : ℕ) {s t : ℕ → Bool} (htail : ∀ k, n ≤ k → s k = t k)
    (hs : ∀ k, k < n → F s k = s k) (ht : ∀ k, k < n → F t k = t k) : s = t := by
  by_contra hne
  obtain ⟨k, hk, hw⟩ := hex s t hne
  by_cases hkn : k < n
  · exact hk (by rw [← hs k hkn, ← ht k hkn, hw])
  · exact hk (htail k (by omega))

theorem prefixNormalize_of_fixed {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (n : ℕ) (b : ℕ → Bool) (hb : ∀ k, k < n → F b k = b k) :
    prefixNormalize F hex n b = b :=
  prefix_solution_unique hex n (prefixNormalize_tail hex n b) (prefixNormalize_fixed hex n b) hb

/-- The normalizer depends only on the frozen tail, not on the discarded prefix. -/
theorem prefixNormalize_tail_local {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (n : ℕ) {b d : ℕ → Bool} (hbd : ∀ k, n ≤ k → b k = d k) :
    prefixNormalize F hex n b = prefixNormalize F hex n d :=
  prefix_solution_unique hex n (fun k hk => by
    rw [prefixNormalize_tail hex n b k hk, prefixNormalize_tail hex n d k hk, hbd k hk])
    (prefixNormalize_fixed hex n b) (prefixNormalize_fixed hex n d)

/-- All finite elimination operators commute; composing them keeps the larger prefix. -/
theorem prefixNormalize_comp {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (m n : ℕ) (b : ℕ → Bool) :
    prefixNormalize F hex m (prefixNormalize F hex n b) = prefixNormalize F hex (max m n) b := by
  by_cases hmn : m ≤ n
  · rw [max_eq_right hmn]
    apply prefixNormalize_of_fixed
    intro k hk
    exact prefixNormalize_fixed hex n b k (lt_of_lt_of_le hk hmn)
  · have hnm : n ≤ m := by omega
    rw [max_eq_left hnm]
    apply prefixNormalize_tail_local
    intro k hk
    exact prefixNormalize_tail hex n b k (le_trans hnm hk)

/-- Full Baire class one is preserved by each finite elimination operator.
The finite solver is applied to the entire finite truth table, not to an
unjustified claim that the approximating maps remain exclusive. -/
theorem baireOne_prefixNormalize {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (hB : BaireOne F) (n : ℕ) : BaireOne (prefixNormalize F hex n) := by
  classical
  obtain ⟨g, hg, hlim⟩ := hB
  let A := Fin n → Bool
  let glue : A → (ℕ → Bool) → ℕ → Bool :=
    fun a b k => if hk : k < n then a ⟨k, hk⟩ else b k
  have hglue : ∀ a, Continuous (glue a) := fun a => continuous_pi fun k => by
    by_cases hk : k < n
    · simpa [glue, hk] using (continuous_const : Continuous fun _ : (ℕ → Bool) => a ⟨k, hk⟩)
    · simpa [glue, hk] using (continuous_apply k : Continuous fun b : (ℕ → Bool) => b k)
  let pick : (A → A) → A := fun v => if h : ∃ a, v a = a then Classical.choose h else fun _ => false
  have hpick : Continuous pick := continuous_of_discreteTopology
  let sig : ((ℕ → Bool) → (ℕ → Bool)) → (ℕ → Bool) → A → A :=
    fun H b a j => H (glue a b) j
  have hsig : ∀ m, Continuous (sig (g m)) := fun m => continuous_pi fun a => continuous_pi fun j =>
    (continuous_apply (j : ℕ)).comp ((hg m).comp (hglue a))
  have hexists : ∀ b, ∃ a, sig F b a = a := by
    intro b
    let x := prefixNormalize F hex n b
    let a : A := fun j => x j
    have hax : glue a b = x := funext fun k => by
      by_cases hk : k < n
      · simp [glue, a, hk]
      · simpa [glue, hk, x] using (prefixNormalize_tail hex n b k (by omega)).symm
    refine ⟨a, funext fun j => ?_⟩
    change F (glue a b) j = x j
    rw [hax]
    exact prefixNormalize_fixed hex n b j j.isLt
  have hreal : ∀ b, glue (pick (sig F b)) b = prefixNormalize F hex n b := by
    intro b
    have hp : sig F b (pick (sig F b)) = pick (sig F b) := by
      dsimp only [pick]
      rw [dite_eq_left (hexists b)]
      exact Classical.choose_spec (hexists b)
    apply prefix_solution_unique hex n
    · intro k hk
      rw [prefixNormalize_tail hex n b k hk]
      simp [glue, show ¬ k < n by omega]
    · intro k hk
      have := congrFun hp (⟨k, hk⟩ : Fin n)
      simpa [sig, glue, hk] using this
    · exact prefixNormalize_fixed hex n b
  refine ⟨fun m b => glue (pick (sig (g m) b)) b, fun m => continuous_pi fun k => ?_, fun b => ?_⟩
  · by_cases hk : k < n
    · simpa [glue, hk, Function.comp_def] using
        (continuous_apply (⟨k, hk⟩ : Fin n)).comp (hpick.comp (hsig m))
    · simpa [glue, hk] using (continuous_apply k : Continuous fun b : (ℕ → Bool) => b k)
  · have heq : ∀ᶠ m in atTop, sig (g m) b = sig F b := by
      have hh : ∀ a : A, ∀ j : Fin n, ∀ᶠ m in atTop,
          g m (glue a b) j = F (glue a b) j := fun a j =>
        eventually_eq_of_tendsto_bool (((continuous_apply (j : ℕ)).tendsto (F (glue a b))).comp
          (hlim (glue a b)))
      have hall := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hh a))
      exact hall.mono fun m hm => funext fun a => funext fun j => hm a j
    exact tendsto_const_nhds.congr' (heq.mono fun m hm => by
      change prefixNormalize F hex n b = glue (pick (sig (g m) b)) b
      rw [hm, hreal b])

/-- Any pointwise limit of the normalizers is invariant under finite input changes. -/
theorem normalizer_limit_tail_invariant {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {L : (ℕ → Bool) → (ℕ → Bool)}
    (hL : ∀ b, Tendsto (fun n => prefixNormalize F hex n b) atTop (𝓝 (L b)))
    {b d : ℕ → Bool} (hbd : {k | b k ≠ d k}.Finite) : L b = L d := by
  obtain ⟨N, hN⟩ := hbd.bddAbove
  have heq : ∀ᶠ n in atTop, prefixNormalize F hex n b = prefixNormalize F hex n d := by
    filter_upwards [eventually_gt_atTop N] with n hn
    apply prefixNormalize_tail_local
    intro k hk
    by_contra h
    have := hN h
    omega
  exact tendsto_nhds_unique (hL b) ((hL d).congr' (heq.mono fun _ h => h.symm))

/-- A Boolean Baire-one tail-invariant observable is constant. Finite-coordinate
changes approximate every point, while class one supplies a continuity point. -/
theorem eq_of_baireOne_tail_invariant_bool {h : (ℕ → Bool) → Bool} (hB : BaireOne h)
    (hinv : ∀ b d, {k | b k ≠ d k}.Finite → h b = h d) (b d : ℕ → Bool) : h b = h d := by
  obtain ⟨z, -, hz⟩ := exists_continuousAt_of_baireOne hB isOpen_univ
    (show (Set.univ : Set (ℕ → Bool)).Nonempty from ⟨fun _ => false, mem_univ _⟩)
  have heq : ∀ a : ℕ → Bool, h a = h z := by
    intro a
    let patch : ℕ → ℕ → Bool := fun n k => if k < n then z k else a k
    have hpatch : Tendsto patch atTop (𝓝 z) := tendsto_pi_nhds.mpr fun k =>
      tendsto_const_nhds.congr' ((eventually_gt_atTop k).mono fun n hn => by simp [patch, hn])
    have hv : ∀ n, h (patch n) = h a := fun n => hinv (patch n) a
      ((Set.finite_lt_nat n).subset fun k hk => by
        by_contra hkn
        exact hk (by simp [patch, show ¬ k < n from hkn]))
    have hh : Tendsto (fun _ : ℕ => h a) atTop (𝓝 (h z)) := by
      simpa only [Function.comp_def, hv] using hz.tendsto.comp hpatch
    exact tendsto_nhds_unique tendsto_const_nhds hh
  exact (heq b).trans (heq d).symm

/-- If finite elimination has a pointwise limit which remains class one, that limit
cannot retain any dependence on the boundary: it is a constant map. Existence or
Baire-one regularity of this infinite-stage limit is not automatic. -/
theorem normalizer_baireOne_limit_constant
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {L : (ℕ → Bool) → (ℕ → Bool)} (hB : BaireOne L)
    (hL : ∀ b, Tendsto (fun n => prefixNormalize F hex n b) atTop (𝓝 (L b))) :
    ∀ b d, L b = L d := by
  intro b d
  apply funext
  intro k
  obtain ⟨g, hg, hlim⟩ := hB
  apply eq_of_baireOne_tail_invariant_bool
    (hB := ⟨fun n x => g n x k, fun n => (continuous_apply k).comp (hg n),
      fun x => ((continuous_apply k).tendsto (L x)).comp (hlim x)⟩)
  intro a a' haa'
  exact congrFun (normalizer_limit_tail_invariant hex hL haa') k

/-- A cluster point of increasingly solved prefixes is a true solution if all
finite elimination operators are continuous there. Relative continuity on the
cluster set alone is NOT the hypothesis. -/
theorem fixed_of_normalizer_cluster_continuity
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {x : ℕ → ℕ → Bool} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hx : ∀ n k, k < n → F (x n) k = x n k)
    {p : ℕ → Bool} (hlim : Tendsto (x ∘ φ) atTop (𝓝 p))
    (hc : ∀ m, ContinuousAt (prefixNormalize F hex m) p) : F p = p := by
  have hfix : ∀ m, prefixNormalize F hex m p = p := by
    intro m
    have heq : ∀ᶠ n in atTop,
        prefixNormalize F hex m (x (φ n)) = x (φ n) := by
      filter_upwards [hφ.eventually_ge_atTop m] with n hn
      apply prefixNormalize_of_fixed
      intro k hk
      exact hx (φ n) k (lt_of_lt_of_le hk hn)
    have hnormlim : Tendsto (fun n => prefixNormalize F hex m (x (φ n))) atTop
        (𝓝 (prefixNormalize F hex m p)) := (hc m).tendsto.comp hlim
    exact tendsto_nhds_unique hnormlim (hlim.congr' (heq.mono fun _ h => h.symm))
  apply funext
  intro k
  have h := prefixNormalize_fixed hex (k+1) p k (by omega)
  rwa [hfix] at h

/-- A self-returning finite-elimination limit with only finitely many remaining
errors cannot be a false candidate. -/
theorem fixed_of_normalizer_self_limit_finite_defect
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F) (p : ℕ → Bool)
    (hlim : Tendsto (fun n => prefixNormalize F hex n p) atTop (𝓝 p))
    (hfin : {k | F p k ≠ p k}.Finite) : F p = p := by
  obtain ⟨M, hM⟩ := hfin.bddAbove
  let N := M+1
  have hag : ∀ k ∈ Finset.range N, ∀ᶠ n in atTop, prefixNormalize F hex n p k = p k :=
    fun k _ => eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto p).comp hlim)
  obtain ⟨n, hn1, hn2⟩ := (((Filter.eventually_all_finset _).mpr hag).and
    (eventually_ge_atTop N)).exists
  apply fixed_of_prefix_agree hex p (x := fun n => prefixNormalize F hex n p)
    (prefixNormalize_tail hex · p) (prefixNormalize_fixed hex · p) (N := N)
    (fun _ _ => rfl) (fun k hk => ?_) hn2 (fun k hk => hn1 k (Finset.mem_range.mpr hk))
  by_contra h
  have := hM h
  dsimp [N] at hk
  omega

end PFUL.Infinite


#print axioms PFUL.Infinite.prefix_solution_unique
#print axioms PFUL.Infinite.prefixNormalize_comp
#print axioms PFUL.Infinite.baireOne_prefixNormalize
#print axioms PFUL.Infinite.normalizer_limit_tail_invariant

#print axioms PFUL.Infinite.eq_of_baireOne_tail_invariant_bool
#print axioms PFUL.Infinite.normalizer_baireOne_limit_constant

#print axioms PFUL.Infinite.fixed_of_normalizer_cluster_continuity
#print axioms PFUL.Infinite.fixed_of_normalizer_self_limit_finite_defect
