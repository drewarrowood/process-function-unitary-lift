/-
# Constant-off-a-set maps (intermediate-classes note §8, items 1–2)

`F` equals a constant `c` off a set `S`.
* `const_mem_of_fpf` : FPF ⇒ `c ∈ S`.
* `box_subset` : exclusive ⇒ the box `s ⊕ cube{k | F s k ≠ c k}` lies in `S`.
* `finite_defect_of_countable` : exclusive, `S` countable ⇒ `{k | F s k ≠ c k}` finite.
* `baireOne_of_const_off_countable_closed` : `S` countable closed ⇒ `F` Baire class 1
  (any values on `S`, any target space).
-/
import PFUL.BaireClasses

open Set Filter Topology

namespace PFUL.Infinite

section Reduction
variable {ι : Type*} {F : (ι → Bool) → (ι → Bool)} {S : Set (ι → Bool)} {c : ι → Bool}

theorem const_mem_of_fpf (hfp : ∀ s, F s ≠ s) (hF : ∀ x, x ∉ S → F x = c) : c ∈ S := by
  by_contra h; exact hfp c (hF c h)

/-- **Box closure.** If `t` differs from `s ∈ S` only where `F s` differs from `c`, then
`t ∈ S`. -/
theorem box_subset (hex : Exclusive F) (hF : ∀ x, x ∉ S → F x = c) {s : ι → Bool} (hs : s ∈ S)
    (t : ι → Bool) (ht : ∀ k, s k ≠ t k → F s k ≠ c k) : t ∈ S := by
  by_contra htS
  have hne : s ≠ t := fun h => htS (h ▸ hs)
  obtain ⟨k, hk, hw⟩ := hex s t hne
  exact ht k hk (by rw [hw, hF t htS])

lemma not_countable_fun_bool_of_infinite (Z : Type*) [Infinite Z] : ¬ Countable (Z → Bool) := by
  classical
  intro hc
  have hr : Function.Surjective fun g : Z → Bool => g ∘ (Infinite.natEmbedding Z) :=
    (Infinite.natEmbedding Z).injective.surjective_comp_right
  have : Countable (ℕ → Bool) := hr.countable
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  have hs : Function.Surjective fun g : ℕ → Bool => {n | g n = true} := fun A =>
    ⟨fun n => decide (n ∈ A), by ext n; simp⟩
  exact Function.cantor_surjective _ (hs.comp hf)

/-- **Finite defect.** With `S` countable, `F s` differs from `c` in finitely many places. -/
theorem finite_defect_of_countable (hex : Exclusive F) (hF : ∀ x, x ∉ S → F x = c)
    (hS : S.Countable) {s : ι → Bool} (hs : s ∈ S) : {k | F s k ≠ c k}.Finite := by
  classical
  by_contra hinf
  set Z := {k | F s k ≠ c k}
  have : Infinite Z := Set.infinite_coe_iff.2 hinf
  let φ : (Z → Bool) → (ι → Bool) := fun d k => if h : k ∈ Z then d ⟨k, h⟩ else s k
  have hφ : Function.Injective φ := fun d d' h => funext fun ⟨k, hk⟩ => by
    have := congrFun h k; simpa [φ, hk] using this
  have hrange : ∀ d, φ d ∈ S := fun d => box_subset hex hF hs (φ d) fun k hk => by
    by_contra hz
    exact hk (by simp [φ, show k ∉ Z from fun h => h hz])
  have : Countable (Z → Bool) := by
    have := hS.to_subtype
    exact Function.Injective.countable (f := fun d => (⟨φ d, hrange d⟩ : S))
      fun d d' h => hφ (congrArg Subtype.val h)
  exact not_countable_fun_bool_of_infinite Z this

end Reduction

section ClassOne

lemma continuous_of_prefix_dep {Y : Type*} [TopologicalSpace Y] {g : (ℕ → Bool) → Y} (n : ℕ)
    (h : ∀ x y, (∀ j < n, x j = y j) → g x = g y) : Continuous g := by
  rw [continuous_iff_continuousAt]; intro x
  have hj : ∀ j ∈ Finset.range n, ∀ᶠ y in 𝓝 x, y j = x j := fun j _ =>
    eventually_eq_of_tendsto_bool ((continuous_apply j).tendsto x)
  have hev : ∀ᶠ y in 𝓝 x, g x = g y :=
    ((Filter.eventually_all_finset _).2 hj).mono fun y hy =>
      h x y fun j hjn => (hy j (Finset.mem_range.2 hjn)).symm
  exact tendsto_const_nhds.congr' hev

/-- Points outside a closed set: a long enough prefix keeps you outside. -/
lemma eventually_prefix_notMem {S : Set (ℕ → Bool)} (hc : IsClosed S) {x : ℕ → Bool}
    (hx : x ∉ S) : ∀ᶠ n in atTop, ∀ y, (∀ j < n, y j = x j) → y ∉ S := by
  have hmem : Sᶜ ∈ 𝓝 x := hc.isOpen_compl.mem_nhds hx
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := hmem
  obtain ⟨N, hN⟩ := hI.bddAbove
  filter_upwards [eventually_gt_atTop N] with n hn y hy
  apply hsub
  intro i hi
  have : y i = x i := hy i (lt_of_le_of_lt (hN hi) hn)
  rw [this]; exact mem_of_mem_nhds (ht i)

/-- **Countable closed perturbation is class 1.** -/
theorem baireOne_of_const_off_countable_closed {Y : Type*} [TopologicalSpace Y]
    {F : (ℕ → Bool) → Y} {S : Set (ℕ → Bool)} (hS : S.Countable) (hc : IsClosed S) (c : Y)
    (hF : ∀ x, x ∉ S → F x = c) : BaireOne F := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => fun _ => c, fun _ => continuous_const, fun x => ?_⟩
    rw [hF x (notMem_empty x)]; exact tendsto_const_nhds
  obtain ⟨e, rfl⟩ := hS.exists_eq_range hne
  let pick : (ℕ → Prop) → Y := fun Q => if h : ∃ j, Q j then F (e (Nat.find h)) else c
  let P : ℕ → (ℕ → Bool) → ℕ → Prop := fun n x j => j < n ∧ ∀ i < n, e j i = x i
  refine ⟨fun n x => pick (P n x), fun n => continuous_of_prefix_dep n fun x y hxy => ?_,
    fun x => ?_⟩
  · have : P n x = P n y := funext fun j => propext <| and_congr_right fun _ =>
      forall₂_congr fun i hi => by rw [hxy i hi]
    simp only [this]
  · by_cases hx : x ∈ range e
    · have hex : ∃ i, e i = x := hx
      set i0 := Nat.find hex
      have hi0 : e i0 = x := Nat.find_spec hex
      have hfar : ∀ j ∈ Finset.range i0, ∀ᶠ n in atTop, ¬ ∀ i < n, e j i = x i := by
        intro j hj
        have hne : e j ≠ x := Nat.find_min hex (Finset.mem_range.1 hj)
        obtain ⟨m, hm⟩ := Function.ne_iff.1 hne
        filter_upwards [eventually_gt_atTop m] with n hn h using hm (h m hn)
      have hev : ∀ᶠ n in atTop, pick (P n x) = F x := by
        filter_upwards [(Filter.eventually_all_finset _).2 hfar, eventually_gt_atTop i0]
          with n hn hgt
        have hP : ∃ j, P n x j := ⟨i0, hgt, fun i _ => by rw [hi0]⟩
        have hfind : Nat.find hP = i0 := by
          rw [Nat.find_eq_iff]
          refine ⟨⟨hgt, fun i _ => by rw [hi0]⟩, fun j hj hPj => ?_⟩
          exact hn j (Finset.mem_range.2 hj) hPj.2
        dsimp only [pick]
        rw [dif_pos hP]
        have h2 : ∀ inst : DecidablePred (P n x), @Nat.find _ inst hP = i0 :=
          fun inst => by convert hfind
        rw [h2, hi0]
      exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
    · have hev : ∀ᶠ n in atTop, pick (P n x) = F x := by
        filter_upwards [eventually_prefix_notMem hc hx] with n hn
        have hP : ¬ ∃ j, P n x j := fun ⟨j, _, hj⟩ => hn (e j) hj (mem_range_self j)
        dsimp only [pick]
        rw [dif_neg hP, hF x hx]
      exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)

end ClassOne

section Prefix
variable {F : (ℕ → Bool) → (ℕ → Bool)}

/-- **Prefix solutions.** Freezing every coordinate `≥ n` to `c` leaves a finite exclusive
problem, which has a solution. -/
theorem exists_prefix_fixed (hex : Exclusive F) (c : ℕ → Bool) (n : ℕ) :
    ∃ x : ℕ → Bool, (∀ k, n ≤ k → x k = c k) ∧ ∀ k, k < n → F x k = x k := by
  classical
  let glue : ({k // k < n} → Bool) → ℕ → Bool :=
    fun y k => if hk : k < n then y ⟨k, hk⟩ else c k
  have hgc : ∀ y k, n ≤ k → glue y k = c k := fun y k hk => by
    simp [glue, show ¬ k < n by omega]
  let w : ({k // k < n} → Bool) → ({k // k < n} → Bool) := fun y j => F (glue y) j
  have hw : ∀ j : {k // k < n}, Continuous fun y => w y j := fun _ =>
    continuous_of_discreteTopology
  have hex' : FiniteBox.Exclusive w := by
    intro y y' hne
    have hg : glue y ≠ glue y' := fun h => hne (funext fun j => by
      have := congrFun h j; simpa [glue, j.2] using this)
    obtain ⟨k, hk, hF⟩ := hex _ _ hg
    have hkn : k < n := by
      by_contra h; exact hk (by rw [hgc _ _ (by omega), hgc _ _ (by omega)])
    refine ⟨⟨k, hkn⟩, fun h => hk ?_, hF⟩
    simp [glue, hkn, h]
  obtain ⟨y, hy, -⟩ := pf_of_exclusive_continuous (I := fun _ => Bool) (O := fun _ => Bool)
    w hw hex' (fun _ => id)
  refine ⟨glue y, hgc y, fun k hk => ?_⟩
  have := hy ⟨k, hk⟩
  simp only [id, w] at this
  rw [this]; simp [glue, hk]

/-- **Cluster lemma.** Let `x n` solve the prefix problem frozen to `c` beyond `n`. If `y` agrees
with `c` and with `F y` beyond `N`, and some `x n` with `n ≥ N` agrees with `y` below `N`, then
`y` is a fixed point. -/
theorem fixed_of_prefix_agree (hex : Exclusive F) (c : ℕ → Bool) {x : ℕ → ℕ → Bool}
    (hx : ∀ n k, n ≤ k → x n k = c k) (hxF : ∀ n k, k < n → F (x n) k = x n k)
    {y : ℕ → Bool} {N : ℕ} (hyc : ∀ k, N ≤ k → y k = c k) (hyF : ∀ k, N ≤ k → F y k = y k)
    {n : ℕ} (hn : N ≤ n) (hag : ∀ k, k < N → x n k = y k) : F y = y := by
  have hxy : x n = y := by
    by_contra hne
    obtain ⟨k, hk, hw⟩ := hex _ _ hne
    by_cases hkn : n ≤ k
    · exact hk (by rw [hx n k hkn, hyc k (by omega)])
    · by_cases hkN : N ≤ k
      · exact hk (by rw [← hxF n k (by omega), hw, hyF k hkN])
      · exact hk (hag k (by omega))
  funext k
  by_cases hk : k < n
  · rw [← hxy]; exact hxF n k hk
  · exact hyF k (by omega)

/-- **Countable perturbations whose finite-difference part does not accumulate at infinity.**
Suppose `F` is exclusive, equals `c` off a countable `S`, and every limit of points of `S` that
differ finitely from `c` also differs finitely from `c`. Then `F` has a fixed point. This covers
every `S` of bounded support size (after translating by `c`). -/
theorem exists_fixed_of_closure_finite_diff (hex : Exclusive F) {S : Set (ℕ → Bool)}
    {c : ℕ → Bool} (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable)
    (hcl : ∀ y ∈ closure (S ∩ {s | {k | s k ≠ c k}.Finite}), {k | y k ≠ c k}.Finite) :
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
  have hxfin : ∀ n, {k | x n k ≠ c k}.Finite := fun n =>
    (Set.finite_lt_nat n).subset fun k hk => by
      by_contra h; exact hk (hx n k (by simpa using h))
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := x) fun _ => mem_univ _
  have hyc : {k | y k ≠ c k}.Finite := hcl y (mem_closure_of_tendsto hlim
    (Eventually.of_forall fun m => ⟨hxS (φ m), hxfin (φ m)⟩))
  have hyF : {k | F y k ≠ y k}.Finite := by
    by_cases hy : y ∈ S
    · exact ((finite_defect_of_countable hex hF hS hy).union hyc).subset fun k hk => by
        by_contra h
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
        exact hk (by rw [h.1, h.2])
    · exact hyc.subset fun k hk => by
        simpa [hF y hy, ne_comm] using hk
  obtain ⟨N1, hN1⟩ := hyc.bddAbove
  obtain ⟨N2, hN2⟩ := hyF.bddAbove
  set N := N1 + N2 + 1
  have hag : ∀ k ∈ Finset.range N, ∀ᶠ m in atTop, x (φ m) k = y k := fun k _ =>
    eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto y).comp hlim)
  obtain ⟨m, hm1, hm2⟩ := (((Filter.eventually_all_finset _).2 hag).and
    (hφ.tendsto_atTop.eventually_ge_atTop N)).exists
  refine hfp y (fixed_of_prefix_agree hex c hx hxF (N := N) (fun k hk => ?_) (fun k hk => ?_)
    hm2 fun k hk => hm1 k (Finset.mem_range.2 hk))
  · by_contra h; have := hN1 h; omega
  · by_contra h; have := hN2 h; omega

/-- **Bounded defect from `c`.** If the points of `S` that differ finitely from `c` differ from it
in at most `K` places, an exclusive `F` equal to `c` off the countable set `S` has a fixed point.
-/
theorem exists_fixed_of_bounded_diff (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (K : ℕ)
    (hbd : ∀ s ∈ S, {k | s k ≠ c k}.Finite →
      ∀ T : Finset ℕ, (∀ k ∈ T, s k ≠ c k) → T.card ≤ K) : ∃ x, F x = x := by
  classical
  let B : Set (ℕ → Bool) := ⋂ T : Finset ℕ, {s | (∀ k ∈ T, s k ≠ c k) → T.card ≤ K}
  have hB : IsClosed B := isClosed_iInter fun T => by
    have : Continuous fun s : ℕ → Bool => decide ((∀ k ∈ T, s k ≠ c k) → T.card ≤ K) :=
      continuous_of_finset_dep T fun x y hxy => by
        simp only [decide_eq_decide]
        exact imp_congr_left (forall₂_congr fun k hk => by rw [hxy k hk])
    have h := (isClosed_discrete {true}).preimage this
    convert h using 1; ext s; simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, decide_eq_true_eq]
  refine exists_fixed_of_closure_finite_diff hex hF hS fun y hy => ?_
  have hyB : y ∈ B := (closure_minimal (fun s hs => mem_iInter.2 fun T =>
    hbd s hs.1 hs.2 T) hB) hy
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (K + 1)
  have := mem_iInter.1 hyB T (fun k hk => hT hk)
  omega

end Prefix

end PFUL.Infinite

#print axioms PFUL.Infinite.const_mem_of_fpf
#print axioms PFUL.Infinite.box_subset
#print axioms PFUL.Infinite.finite_defect_of_countable
#print axioms PFUL.Infinite.baireOne_of_const_off_countable_closed
#print axioms PFUL.Infinite.exists_prefix_fixed
#print axioms PFUL.Infinite.fixed_of_prefix_agree
#print axioms PFUL.Infinite.exists_fixed_of_closure_finite_diff
#print axioms PFUL.Infinite.exists_fixed_of_bounded_diff
