import PFUL.CountablePerturbation

open Set Filter Topology
namespace PFUL.Infinite

/-- Closedness is not needed to put all finite corners of the limiting box in S. -/
theorem finite_corners_subset_of_prefix_cluster {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c)
    {x : ℕ → ℕ → Bool} (hxS : ∀ n, x n ∈ S)
    (hx : ∀ n k, n ≤ k → x n k = c k)
    (hxF : ∀ n k, k < n → F (x n) k = x n k)
    {φ : ℕ → ℕ} {y : ℕ → Bool} (hlim : Tendsto (x ∘ φ) atTop (𝓝 y))
    {t : ℕ → Bool} (htfin : {k | t k ≠ c k}.Finite)
    (ht : ∀ k, y k ≠ t k → y k ≠ c k) : t ∈ S := by
  have hyt : ∀ k, t k ≠ c k → y k = t k := by
    intro k hk
    have h := ht k
    cases hy : y k <;> cases ht' : t k <;> cases hc' : c k <;> simp_all
  have hag : ∀ k ∈ htfin.toFinset, ∀ᶠ m in atTop, x (φ m) k = y k := fun k _ =>
    eventually_eq_of_tendsto_bool (((continuous_apply k).tendsto y).comp hlim)
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset _).2 hag).exists
  apply box_subset hex hF (hxS (φ m)) t
  intro k hk
  have hxc : x (φ m) k ≠ c k := by
    intro heq
    by_cases htc : t k = c k
    · exact hk (heq.trans htc.symm)
    · have hmem : k ∈ htfin.toFinset := htfin.mem_toFinset.mpr htc
      exact htc ((hyt k htc).symm.trans ((hm k hmem).symm.trans heq))
  have hkn : k < φ m := by
    by_contra h
    exact hxc (hx (φ m) k (by omega))
  rw [hxF (φ m) k hkn]
  exact hxc

/-- With countable exceptional set and no fixed point, some infinitely dimensional
box has every finite corner in the exceptional set. No closedness is assumed. -/
theorem exists_infinite_finite_corner_box_of_fpf_countable
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hfp : ∀ x, F x ≠ x) :
    ∃ y : ℕ → Bool, {k | y k ≠ c k}.Infinite ∧
      ∀ t, {k | t k ≠ c k}.Finite →
        (∀ k, y k ≠ t k → y k ≠ c k) → t ∈ S := by
  choose x hx hxF using exists_prefix_fixed hex c
  have hxS : ∀ n, x n ∈ S := fun n => by
    by_contra h
    have hxc : x n = c := funext fun k => by
      by_cases hk : k < n
      · rw [← hxF n k hk, hF _ h]
      · exact hx n k (by omega)
    exact hfp (x n) (by rw [hF _ h, hxc])
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := x) fun _ => mem_univ _
  refine ⟨y, ?_, fun t htfin ht =>
    finite_corners_subset_of_prefix_cluster hex hF hxS hx hxF hlim htfin ht⟩
  intro hyc
  have hyout : {k | F y k ≠ c k}.Finite := by
    by_cases hyS : y ∈ S
    · exact finite_defect_of_countable hex hF hS hyS
    · simp [hF y hyS]
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

/-- An infinite Boolean product has no singleton with nonempty interior. -/
lemma bool_product_interior_singleton {Z : Type*} [Infinite Z] (d : Z → Bool) :
    interior ({d} : Set (Z → Bool)) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxd : x = d := mem_singleton_iff.mp (interior_subset hx)
  subst x
  have hmem : ({d} : Set (Z → Bool)) ∈ 𝓝 d := mem_interior_iff_mem_nhds.mp hx
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := hmem
  obtain ⟨z, hz⟩ := hI.exists_notMem
  have hu : Function.update d z (!d z) = d := mem_singleton_iff.mp (hsub (by
    intro i hi
    rw [Function.update_of_ne (show i ≠ z from fun heq => hz (heq ▸ hi))]
    exact mem_of_mem_nhds (ht i)))
  have hbad := congrFun hu z
  simp at hbad

/-- Baire category excludes a countable dense G-delta in an infinite Boolean product. -/
lemma not_countable_dense_isGδ_bool_product {Z : Type*} [Infinite Z]
    {A : Set (Z → Bool)} (hA : A.Countable) (hG : IsGδ A) (hd : Dense A) : False := by
  have he : Dense (∅ : Set (Z → Bool)) := by
    simpa only [bool_product_interior_singleton, iUnion_empty] using
      hG.dense_biUnion_interior_of_closed hd hA (fun a _ => isClosed_singleton)
        (show A ⊆ ⋃ a ∈ A, ({a} : Set (Z → Bool)) by simp)
  exact Set.not_nonempty_empty he.nonempty

/-- Countability plus G-delta regularity already rules out an infinite finite-corner box. -/
theorem finite_diff_of_countable_isGδ_finite_corners {S : Set (ℕ → Bool)}
    (hS : S.Countable) (hG : IsGδ S) {y c : ℕ → Bool}
    (hcorners : ∀ t, {k | t k ≠ c k}.Finite →
      (∀ k, y k ≠ t k → y k ≠ c k) → t ∈ S) : {k | y k ≠ c k}.Finite := by
  classical
  by_contra hinf
  let Z := {k | y k ≠ c k}
  have : Infinite Z := Set.infinite_coe_iff.2 hinf
  let embed : (Z → Bool) → ℕ → Bool :=
    fun d k => if hk : k ∈ Z then d ⟨k, hk⟩ else c k
  have hemb : Continuous embed := continuous_pi fun k => by
    by_cases hk : k ∈ Z
    · simpa [embed, hk] using (continuous_apply (⟨k, hk⟩ : Z))
    · simpa [embed, hk] using (continuous_const : Continuous fun _ : (Z → Bool) => c k)
  have hinj : Function.Injective embed := fun d d' h => funext fun ⟨k, hk⟩ => by
    have := congrFun h k
    simpa [embed, hk] using this
  have hdense : Dense (embed ⁻¹' S) := by
    intro d
    let trunc : ℕ → Z → Bool := fun n k => if (k : ℕ) < n then d k else c k
    have hlim : Tendsto trunc atTop (𝓝 d) := tendsto_pi_nhds.mpr fun k =>
      tendsto_const_nhds.congr' ((eventually_gt_atTop (k : ℕ)).mono fun n hn => by
        simp [trunc, hn])
    apply mem_closure_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    apply hcorners (embed (trunc n))
    · apply (Set.finite_lt_nat n).subset
      intro k hk
      by_contra hkn
      apply hk
      by_cases hz : k ∈ Z <;> simp [embed, trunc, hz, show ¬ k < n from hkn]
    · intro k hk
      by_cases hz : k ∈ Z
      · exact hz
      · have heq : y k = c k := by simpa [Z] using hz
        exact (hk (by simp [embed, hz, heq])).elim
  exact not_countable_dense_isGδ_bool_product (hS.preimage hinj) (hG.preimage hemb) hdense

/-- **Countable G-delta perturbation theorem.** Closedness can be weakened to G-delta. -/
theorem exists_fixed_of_const_off_countable_isGδ {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hG : IsGδ S) :
    ∃ x, F x = x := by
  by_contra hfp
  push Not at hfp
  obtain ⟨y, hy, hcorners⟩ := exists_infinite_finite_corner_box_of_fpf_countable hex hF hS hfp
  exact hy (finite_diff_of_countable_isGδ_finite_corners hS hG hcorners)

/-- A fixed-point-free countably supported exclusive map must have a non-G-delta
actual exceptional set. This statement needs no assumption about Baire class. -/
theorem not_isGδ_exceptional_of_fpf_countable {F : (ℕ → Bool) → (ℕ → Bool)}
    (hex : Exclusive F) {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hfp : ∀ x, F x ≠ x) :
    ¬ IsGδ {x | F x ≠ c} := by
  intro hG
  have hE : {x | F x ≠ c}.Countable := hS.mono fun x hx => by
    by_contra h
    exact hx (hF x h)
  obtain ⟨x, hx⟩ := exists_fixed_of_const_off_countable_isGδ hex
    (S := {x | F x ≠ c}) (c := c) (fun x hx => by simpa using hx) hE hG
  exact hfp x hx

/-- Discrete Boolean fibers of pointwise limits of continuous maps are G-delta. -/
theorem isGδ_fiber_of_baireOne_bool {X : Type*} [TopologicalSpace X]
    {f : X → Bool} (hf : BaireOne f) (b : Bool) : IsGδ {x | f x = b} := by
  obtain ⟨g, hg, hlim⟩ := hf
  let U : ℕ → Set X := fun N => ⋃ n, ⋃ (_ : N ≤ n), {x | g n x = b}
  have hU : ∀ N, IsOpen (U N) := fun N => isOpen_iUnion fun n => isOpen_iUnion fun _ =>
    (isOpen_discrete ({b} : Set Bool)).preimage (hg n)
  have heq : {x | f x = b} = ⋂ N, U N := by
    ext x
    obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_eq_of_tendsto_bool (hlim x))
    constructor
    · intro hx
      apply mem_iInter.mpr
      intro N
      exact mem_iUnion.mpr ⟨max N M, mem_iUnion.mpr ⟨le_max_left _ _, by
        dsimp
        rw [hM _ (le_max_right _ _), hx]⟩⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (mem_iInter.mp hx M)
      obtain ⟨hnM, hnb⟩ := mem_iUnion.mp hn
      exact (hM n hnM).symm.trans hnb
  rw [heq]
  exact IsGδ.iInter_of_isOpen hU

/-- Thus a hypothetical countably supported Baire-one counterexample has G-delta
individual coordinate defects, despite its entire exceptional set not being G-delta. -/
theorem isGδ_coordinate_defect_of_baireOne {F : (ℕ → Bool) → (ℕ → Bool)}
    (hB : BaireOne F) (c : ℕ → Bool) (k : ℕ) : IsGδ {x | F x k ≠ c k} := by
  obtain ⟨g, hg, hlim⟩ := hB
  have hcoord : BaireOne (fun x => F x k) :=
    ⟨fun n x => g n x k, fun n => (continuous_apply k).comp (hg n),
      fun x => ((continuous_apply k).tendsto (F x)).comp (hlim x)⟩
  convert isGδ_fiber_of_baireOne_bool hcoord (!(c k)) using 1
  ext x
  cases h : F x k <;> cases hc : c k <;> simp

/-- Arbitrary values on a countable G-delta set, constant values elsewhere, are
pointwise limits of continuous maps. No regularity of the values on S is needed. -/
theorem baireOne_of_const_off_countable_isGδ {Y : Type*} [TopologicalSpace Y]
    {F : (ℕ → Bool) → Y} {S : Set (ℕ → Bool)} (hS : S.Countable) (hG : IsGδ S) (c : Y)
    (hF : ∀ x, x ∉ S → F x = c) : BaireOne F := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => fun _ => c, fun _ => continuous_const, fun x => ?_⟩
    rw [hF x (notMem_empty x)]
    exact tendsto_const_nhds
  obtain ⟨U, hU, hSU⟩ := hG.eq_iInter_nat
  obtain ⟨e, he⟩ := hS.exists_eq_range hne
  have heS : ∀ j, e j ∈ S := fun j => he ▸ mem_range_self j
  have hp : ∀ n, ∃ L : ℕ, n ≤ L ∧ ∀ j : Fin n, ∀ i : Fin n,
      ∀ x, (∀ k < L, e j k = x k) → x ∈ U i := by
    intro n
    have hv : ∀ j : Fin n, ∀ i : Fin n, ∀ᶠ L in atTop,
        ∀ x, (∀ k < L, e j k = x k) → x ∈ U i := by
      intro j i
      have hej : e j ∉ (U i)ᶜ := by
        simpa using mem_iInter.mp (hSU ▸ heS j) (i : ℕ)
      filter_upwards [eventually_prefix_notMem (hU i).isClosed_compl hej] with L hL x hx
      simpa using hL x (fun k hk => (hx k hk).symm)
    have hall : ∀ᶠ L in atTop, ∀ j : Fin n, ∀ i : Fin n,
        ∀ x, (∀ k < L, e j k = x k) → x ∈ U i :=
      Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr (hv j)
    exact ((eventually_ge_atTop n).and hall).exists
  choose L hLn hL using hp
  let pick : (ℕ → Prop) → Y := fun Q => if h : ∃ j, Q j then F (e (Nat.find h)) else c
  let P : ℕ → (ℕ → Bool) → ℕ → Prop := fun n x j => j < n ∧ ∀ i < L n, e j i = x i
  refine ⟨fun n x => pick (P n x), fun n => continuous_of_prefix_dep (L n) (fun x y hxy => ?_),
    fun x => ?_⟩
  · have : P n x = P n y := funext fun j => propext <| and_congr_right fun _ =>
      forall₂_congr fun i hi => by rw [hxy i hi]
    simp only [this]
  · by_cases hx : x ∈ S
    · have hex : ∃ i, e i = x := Set.mem_range.mp (he ▸ hx)
      let i0 := Nat.find hex
      have hi0 : e i0 = x := Nat.find_spec hex
      have hfar : ∀ j ∈ Finset.range i0, ∀ᶠ n in atTop, ¬ ∀ i < L n, e j i = x i := by
        intro j hj
        have hne : e j ≠ x := Nat.find_min hex (Finset.mem_range.mp hj)
        obtain ⟨m, hm⟩ := Function.ne_iff.mp hne
        filter_upwards [eventually_gt_atTop m] with n hn h
        exact hm (h m (lt_of_lt_of_le hn (hLn n)))
      have hev : ∀ᶠ n in atTop, pick (P n x) = F x := by
        filter_upwards [(Filter.eventually_all_finset _).mpr hfar, eventually_gt_atTop i0]
          with n hn hgt
        have hP : ∃ j, P n x j := ⟨i0, hgt, fun i _ => by rw [hi0]⟩
        have hfind : Nat.find hP = i0 := by
          rw [Nat.find_eq_iff]
          refine ⟨⟨hgt, fun i _ => by rw [hi0]⟩, fun j hj hPj => ?_⟩
          exact hn j (Finset.mem_range.mpr hj) hPj.2
        dsimp only [pick]
        rw [dite_eq_left hP]
        have h2 : ∀ inst : DecidablePred (P n x), @Nat.find _ inst hP = i0 :=
          fun inst => by convert hfind
        rw [h2, hi0]
      exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
    · have hnall : ¬ ∀ i, x ∈ U i := fun h => hx (hSU ▸ mem_iInter.mpr h)
      push Not at hnall
      obtain ⟨i, hi⟩ := hnall
      have hev : ∀ᶠ n in atTop, pick (P n x) = F x := by
        filter_upwards [eventually_gt_atTop i] with n hn
        have hP : ¬ ∃ j, P n x j := by
          rintro ⟨j, hj, hprefix⟩
          exact hi (hL n ⟨j, hj⟩ ⟨i, hn⟩ x hprefix)
        dsimp only [pick]
        rw [dite_eq_right hP, hF x hx]
      exact tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)

/-- Exact regularity criterion for a countably supported Boolean-valued product map:
class one is equivalent to G-delta regularity of each coordinate defect set.
The union of those sets need not be G-delta. -/
theorem baireOne_iff_coordinate_defects_isGδ_of_const_off_countable
    {F : (ℕ → Bool) → (ℕ → Bool)} {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) :
    BaireOne F ↔ ∀ k, IsGδ {x | F x k ≠ c k} := by
  constructor
  · intro hB k
    exact isGδ_coordinate_defect_of_baireOne hB c k
  · intro hG
    have hb : ∀ k, BaireOne (fun x => F x k) := fun k =>
      baireOne_of_const_off_countable_isGδ
        (hS.mono (fun x hx => by
          by_contra h
          exact hx (congrFun (hF x h) k))) (hG k) (c k)
        (fun x hx => by simpa using hx)
    choose g hg hlim using hb
    refine ⟨fun n x k => g k n x, fun n => continuous_pi fun k => hg k n, fun x => ?_⟩
    exact tendsto_pi_nhds.mpr fun k => hlim k x

theorem exists_unique_fixed_of_const_off_countable_isGδ
    {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    {S : Set (ℕ → Bool)} {c : ℕ → Bool}
    (hF : ∀ x, x ∉ S → F x = c) (hS : S.Countable) (hG : IsGδ S) :
    ∃! x, F x = x := by
  obtain ⟨x, hx⟩ := exists_fixed_of_const_off_countable_isGδ hex hF hS hG
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  obtain ⟨k, hk, hw⟩ := hex y x hne
  rw [hy, hx] at hw
  exact hk hw

end PFUL.Infinite

#print axioms PFUL.Infinite.finite_corners_subset_of_prefix_cluster
#print axioms PFUL.Infinite.exists_infinite_finite_corner_box_of_fpf_countable

#print axioms PFUL.Infinite.finite_diff_of_countable_isGδ_finite_corners
#print axioms PFUL.Infinite.exists_fixed_of_const_off_countable_isGδ

#print axioms PFUL.Infinite.not_isGδ_exceptional_of_fpf_countable
#print axioms PFUL.Infinite.isGδ_fiber_of_baireOne_bool
#print axioms PFUL.Infinite.isGδ_coordinate_defect_of_baireOne

#print axioms PFUL.Infinite.baireOne_of_const_off_countable_isGδ

#print axioms PFUL.Infinite.baireOne_iff_coordinate_defects_isGδ_of_const_off_countable

#print axioms PFUL.Infinite.exists_unique_fixed_of_const_off_countable_isGδ
