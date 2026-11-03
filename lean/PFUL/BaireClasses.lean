/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Descriptive complexity of exclusive fixed-point-free maps

* `BaireOne f`: `f` is a pointwise limit of continuous maps (for `Bool`-valued `f` on `ℕ → Bool`
  this is Baire class 1).
* `exists_continuousAt_of_baireOne`: Baire's theorem for `Bool`-valued class-1 maps on a Baire
  space (every nonempty open set contains a point of continuity).
* `zfcF_measurable`, `finSupp_isFσ`: `zfcF` is Borel; the finite-support set is `F_σ`.
* `zfcF_coord_baireTwo`: each coordinate of `zfcF` is a pointwise limit of class-1 maps.
* `zfcF_coord0_not_baireOne`, `zfcF_not_baireOne`: `zfcF` is not of class 1.
* `exists_subcube_fixed`, `exists_fixed_of_finite_discontinuities`: compactness on subcubes and
  the finitely-many-discontinuities theorem.
* `exists_fixed_of_piece_constant`: the one-discontinuity "constant on pieces" obstruction.
* `exists_exclusive_fixedPointFree_of_infinite`, `exists_exclusive_not_pf_of_infinite`:
  any infinite party set.
* `yablo`: class 1, fixed-point-free, not exclusive.
-/
import PFUL.IntermediateClasses

open Set Filter Topology

namespace PFUL.Infinite

/-- Pointwise limit of continuous maps. -/
def BaireOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∃ g : ℕ → X → Y, (∀ n, Continuous (g n)) ∧ ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))

lemma ite_t {p : Prop} [Decidable p] {a b : Bool} (h : p) : (if p then a else b) = a := by
  simp [h]

lemma ite_f {p : Prop} [Decidable p] {a b : Bool} (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

lemma eventually_eq_of_tendsto_bool {α : Type*} {l : Filter α} {u : α → Bool} {b : Bool}
    (h : Tendsto u l (𝓝 b)) : ∀ᶠ a in l, u a = b := by
  rw [nhds_discrete, tendsto_pure] at h; exact h

lemma tendsto_bool_of_eventually {α : Type*} {l : Filter α} {u : α → Bool} {b : Bool}
    (h : ∀ᶠ a in l, u a = b) : Tendsto u l (𝓝 b) := by
  rw [nhds_discrete, tendsto_pure]; exact h

/-- A `Bool`-valued map depending on finitely many coordinates is continuous. -/
lemma continuous_of_finset_dep {ι : Type*} {g : (ι → Bool) → Bool} (S : Finset ι)
    (h : ∀ x y, (∀ j ∈ S, x j = y j) → g x = g y) : Continuous g := by
  rw [continuous_iff_continuousAt]; intro x
  have hj : ∀ j ∈ S, ∀ᶠ y in 𝓝 x, y j = x j := fun j _ =>
    eventually_eq_of_tendsto_bool ((continuous_apply j).tendsto x)
  exact tendsto_bool_of_eventually
    (((Filter.eventually_all_finset S).2 hj).mono fun y hy => h y x hy)

/-- **Baire's theorem** (`Bool`-valued class 1): every nonempty open set contains a point of
continuity. -/
theorem exists_continuousAt_of_baireOne {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {f : X → Bool} (hf : BaireOne f) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ContinuousAt f x := by
  obtain ⟨g, hg, hlim⟩ := hf
  let A : ℕ → Set X := fun N => {x | ∀ m, N ≤ m → g m x = g N x}
  have hA : ∀ N, IsClosed (A N) := fun N => by
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_eq (hg m) (hg N)
  have hcov : ⋃ N, A N = univ := eq_univ_of_forall fun x => by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_eq_of_tendsto_bool (hlim x))
    exact mem_iUnion.2 ⟨N, fun m hm => (hN m hm).trans (hN N le_rfl).symm⟩
  obtain ⟨x, hxU, hx⟩ := (dense_iUnion_interior_of_closed hA hcov).inter_open_nonempty U hU hne
  obtain ⟨N, hN⟩ := mem_iUnion.1 hx
  have hfg : ∀ y ∈ A N, f y = g N y := fun y hy => by
    obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_eq_of_tendsto_bool (hlim y))
    rw [← hM (max M N) (le_max_left _ _), hy _ (le_max_right _ _)]
  refine ⟨x, hxU, ((hg N).continuousAt).congr ?_⟩
  filter_upwards [isOpen_interior.mem_nhds hN] with y hy
  exact (hfg y (interior_subset hy)).symm

/-! ### zfcF: Borel, exactly class 2 -/

/-- The finite-support set is `F_σ`. -/
theorem finSupp_isFσ : ∃ C : ℕ → Set (ℕ → Bool), (∀ N, IsClosed (C N)) ∧
    {s | FinSupp s} = ⋃ N, C N := by
  refine ⟨fun N => {s | ∀ k, N ≤ k → s k = false}, fun N => ?_, ?_⟩
  · simp only [ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply k) continuous_const
  · ext s; simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · exact bound_of_finSupp
    · rintro ⟨N, hN⟩
      exact (finite_lt_nat N).subset fun k hk => by
        by_contra h; simp only [mem_ofPred_eq, not_lt] at h hk; rw [hN k h] at hk; simp at hk

/-- `zfcF` is Borel measurable (product σ-algebra = Borel σ-algebra on `ℕ → Bool`). -/
theorem zfcF_measurable : Measurable zfcF := by
  classical
  obtain ⟨C, hC, hE⟩ := finSupp_isFσ
  have hEm : MeasurableSet {s : ℕ → Bool | FinSupp s} := by
    rw [hE]; exact MeasurableSet.iUnion fun N => (hC N).measurableSet
  rw [measurable_pi_iff]; intro k
  have : (fun s => zfcF s k) = fun s => if FinSupp s then
      (match k with | 0 => true | k + 1 => s k) else false := by
    funext s; by_cases h : FinSupp s
    · rw [zfcF_fin h, ite_t h]; cases k <;> rfl
    · rw [zfcF_inf h, ite_f h]
  rw [this]
  refine Measurable.ite hEm ?_ measurable_const
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

/-- The same, stated for the Borel σ-algebra of the product topology. -/
theorem zfcF_borel_measurable : @Measurable _ _ (borel (ℕ → Bool)) (borel (ℕ → Bool)) zfcF := by
  rw [← BorelSpace.measurable_eq (α := ℕ → Bool)]; exact zfcF_measurable

/-- The value of coordinate `k` of `zfcF` on finitely supported inputs. -/
def zv : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, s => s k

lemma zfcF_eq_ite (s : ℕ → Bool) (k : ℕ) [Decidable (FinSupp s)] :
    zfcF s k = if FinSupp s then zv k s else false := by
  by_cases h : FinSupp s
  · rw [zfcF_fin h, ite_t h]; cases k <;> rfl
  · rw [zfcF_inf h, ite_f h]

/-- **Class 2.** Each coordinate of `zfcF` is a pointwise limit of class-1 maps. -/
theorem zfcF_coord_baireTwo (k : ℕ) : ∃ h : ℕ → (ℕ → Bool) → Bool,
    (∀ N, BaireOne (h N)) ∧ ∀ s, Tendsto (fun N => h N s) atTop (𝓝 (zfcF s k)) := by
  classical
  refine ⟨fun N s => if ∀ j, N ≤ j → s j = false then zv k s else false, fun N => ?_, fun s => ?_⟩
  · refine ⟨fun M s => if ∀ j ∈ Finset.Ico N M, s j = false then zv k s else false,
      fun M => continuous_of_finset_dep (Finset.range (M + k + 1)) fun x y hxy => ?_, fun s => ?_⟩
    · have h1 : (∀ j ∈ Finset.Ico N M, x j = false) ↔ ∀ j ∈ Finset.Ico N M, y j = false :=
        forall₂_congr fun j hj => by
          rw [hxy j (Finset.mem_range.2 (by simp at hj; omega))]
      have h2 : zv k x = zv k y := by
        cases k with
        | zero => rfl
        | succ k => exact hxy k (Finset.mem_range.2 (by omega))
      simp only [h1, h2]
    · apply tendsto_bool_of_eventually
      by_cases hs : ∀ j, N ≤ j → s j = false
      · exact Eventually.of_forall fun M => by
          have h1 : ∀ j ∈ Finset.Ico N M, s j = false := fun j hj => hs j (Finset.mem_Ico.1 hj).1
          simp only []; rw [ite_t h1, ite_t hs]
      · push Not at hs
        obtain ⟨j, hj, hsj⟩ := hs
        filter_upwards [eventually_gt_atTop j] with M hM
        have hn : ¬ ∀ j ∈ Finset.Ico N M, s j = false := fun h =>
          by simpa [hsj] using h j (Finset.mem_Ico.2 ⟨hj, hM⟩)
        have hn' : ¬ ∀ j, N ≤ j → s j = false := fun h => by simpa [hsj] using h j hj
        show (if _ then _ else _) = (if _ then _ else _)
        rw [ite_f hn, ite_f hn']
  · apply tendsto_bool_of_eventually
    rw [zfcF_eq_ite]
    by_cases hs : FinSupp s
    · obtain ⟨N, hN⟩ := bound_of_finSupp hs
      filter_upwards [eventually_ge_atTop N] with M hM
      show (if _ then _ else _) = _
      rw [ite_t fun j hj => hN j (hM.trans hj), ite_t hs]
    · refine Eventually.of_forall fun N => ?_
      obtain ⟨j, hj, hsj⟩ := exists_true_ge hs N
      have hn : ¬ ∀ j, N ≤ j → s j = false := fun h => by simpa [hsj] using h j hj
      show (if _ then _ else _) = _
      rw [ite_f hn, ite_f hs]

/-- Coordinate 0 of `zfcF` is continuous at no point. -/
theorem zfcF_coord0_not_continuousAt (s : ℕ → Bool) : ¬ ContinuousAt (fun x => zfcF x 0) s :=
  fun h0 => by
  classical
  let ap : Bool → ℕ → ℕ → Bool := fun c n k => if k < n then s k else c
  have hlim : ∀ c, Tendsto (ap c) atTop (𝓝 s) := fun c => by
    rw [tendsto_pi_nhds]; intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [ap, hn]
  have hfin : ∀ n, FinSupp (ap false n) := fun n =>
    (finite_lt_nat n).subset fun k hk => by
      by_contra h; simp only [mem_ofPred_eq, not_lt] at h hk; simp [ap, not_lt.2 h] at hk
  have hinf : ∀ n, ¬ FinSupp (ap true n) := fun n hF => by
    obtain ⟨N, hN⟩ := bound_of_finSupp hF
    have := hN (max n N) (le_max_right _ _); simp [ap] at this
  by_cases hs : FinSupp s
  · have t := h0.tendsto.comp (hlim true)
    rw [show zfcF s 0 = true by rw [zfcF_fin hs]] at t
    have t' : Tendsto (fun _ : ℕ => false) atTop (𝓝 true) :=
      t.congr fun n => zfcF_inf (hinf n) 0
    exact Bool.false_ne_true (tendsto_nhds_unique tendsto_const_nhds t')
  · have t := h0.tendsto.comp (hlim false)
    rw [zfcF_inf hs 0] at t
    have t' : Tendsto (fun _ : ℕ => true) atTop (𝓝 false) :=
      t.congr fun n => by show zfcF (ap false n) 0 = true; rw [zfcF_fin (hfin n)]
    exact Bool.false_ne_true (tendsto_nhds_unique t' tendsto_const_nhds)

/-- **Not class 1.** Coordinate 0 of `zfcF` is not a pointwise limit of continuous maps. -/
theorem zfcF_coord0_not_baireOne : ¬ BaireOne fun s => zfcF s 0 := fun h => by
  obtain ⟨x, -, hx⟩ := exists_continuousAt_of_baireOne h isOpen_univ univ_nonempty
  exact zfcF_coord0_not_continuousAt x hx

theorem zfcF_not_baireOne : ¬ BaireOne zfcF := by
  rintro ⟨g, hg, hlim⟩
  exact zfcF_coord0_not_baireOne ⟨fun n s => g n s 0, fun n => (continuous_apply 0).comp (hg n),
    fun s => ((continuous_apply 0).tendsto _).comp (hlim s)⟩

/-! ### Compactness on subcubes; finitely many discontinuities -/

/-- **Compactness on subcubes.** If `F` is exclusive and continuous at every point of the subcube
`{x | x = b on T}` (`T` finite), the subproblem frozen to `b` has a solution. -/
theorem exists_subcube_fixed {ι : Type*} {F : (ι → Bool) → (ι → Bool)} (hex : Exclusive F)
    (T : Finset ι) (b : ι → Bool) (hc : ∀ x, (∀ k ∈ T, x k = b k) → ContinuousAt F x) :
    ∃ x : ι → Bool, (∀ k ∈ T, x k = b k) ∧ ∀ k, k ∉ T → F x k = x k := by
  classical
  let glue : ({k // k ∉ T} → Bool) → ι → Bool :=
    fun y k => if hk : k ∈ T then b k else y ⟨k, hk⟩
  have hglue : Continuous glue := continuous_pi fun k => by
    by_cases hk : k ∈ T
    · simp only [glue, hk, ↓reduceDIte]; exact continuous_const
    · simp only [glue, hk, ↓reduceDIte]; exact continuous_apply _
  have hgT : ∀ y, ∀ k ∈ T, glue y k = b k := fun y k hk => by simp [glue, hk]
  let w : ({k // k ∉ T} → Bool) → ({k // k ∉ T} → Bool) := fun y j => F (glue y) j
  have hw : ∀ j : {k // k ∉ T}, Continuous fun y => w y j := fun j =>
    (continuous_apply (j : ι)).comp (continuous_iff_continuousAt.2 fun y =>
      (hc _ (hgT y)).comp hglue.continuousAt)
  have hex' : FiniteBox.Exclusive w := by
    intro y y' hne
    have hg : glue y ≠ glue y' := fun h => hne (funext fun j => by
      have := congrFun h j; simpa [glue, j.2] using this)
    obtain ⟨k, hk, hF⟩ := hex _ _ hg
    have hkT : k ∉ T := fun hkT => hk (by rw [hgT _ _ hkT, hgT _ _ hkT])
    refine ⟨⟨k, hkT⟩, fun h => hk ?_, hF⟩
    simp [glue, hkT, h]
  obtain ⟨y, hy, -⟩ := pf_of_exclusive_continuous (I := fun _ => Bool) (O := fun _ => Bool)
    w hw hex' (fun _ => id)
  refine ⟨glue y, hgT y, fun k hk => ?_⟩
  have := hy ⟨k, hk⟩
  simp only [id, w] at this
  rw [this]; simp [glue, hk]

/-- **Finitely many discontinuities.** An exclusive `F`, continuous off a finite set `P`, with
`F p` differing from `p` in finitely many coordinates for each `p ∈ P`, has a fixed point. -/
theorem exists_fixed_of_finite_discontinuities {ι : Type*} {F : (ι → Bool) → (ι → Bool)}
    (hex : Exclusive F) (P : Finset (ι → Bool)) (hc : ∀ x, x ∉ P → ContinuousAt F x)
    (hdef : ∀ p ∈ P, {k | F p k ≠ p k}.Finite) : ∃ s, F s = s := by
  classical
  let T : Finset ι := P.attach.biUnion fun p => (hdef p.1 p.2).toFinset
  refine exists_fixed_of_frozen hex T fun b => ?_
  by_cases hP : ∃ p ∈ P, ∀ k ∈ T, p k = b k
  · obtain ⟨p, hp, hpb⟩ := hP
    refine ⟨p, hpb, fun k hk => ?_⟩
    by_contra hne
    exact hk (Finset.mem_biUnion.2 ⟨⟨p, hp⟩, Finset.mem_attach _ _, by simpa using hne⟩)
  · simp only [not_exists, not_and, not_forall] at hP
    exact exists_subcube_fixed hex T b fun x hx => hc x fun hxP => by
      obtain ⟨k, hk, hne⟩ := hP x hxP; exact hne (hx k hk)

/-! ### One discontinuity, constant on the first piece -/

/-- If `F 0` says "flip party 0", exclusivity forces `F e₀` to have party 0 on; if `F` is constant
on the piece `{s | s 0 = true}`, its value there is a fixed point. -/
theorem exists_fixed_of_piece_constant {F : (ℕ → Bool) → (ℕ → Bool)} (hex : Exclusive F)
    (h0 : F (fun _ => false) 0 = true)
    (hU : ∀ s t, s 0 = true → t 0 = true → F s = F t) : ∃ s, F s = s := by
  let e : ℕ → Bool := fun k => decide (k = 0)
  have hne : (fun _ : ℕ => false) ≠ e := fun h => by simpa [e] using congrFun h 0
  obtain ⟨k, hk, hF⟩ := hex _ _ hne
  have k0 : k = 0 := by by_contra h; exact hk (by simp [e, h])
  subst k0
  have ha : F e 0 = true := hF ▸ h0
  exact ⟨F e, hU _ _ ha (by simp [e])⟩

/-! ### Any infinite set of parties -/

open Classical in
/-- `zfcF` on a copy of `ℕ`, constant `false` elsewhere. -/
noncomputable def zfcFOn {ι : Type*} (e : ℕ ↪ ι) (s : ι → Bool) (k : ι) : Bool :=
  if k ∈ range e then zfcF (s ∘ e) (Function.invFun e k) else false

theorem exists_exclusive_fixedPointFree_of_infinite {ι : Type*} [Infinite ι] :
    ∃ F : (ι → Bool) → (ι → Bool), (∀ s, F s ≠ s) ∧ Exclusive F := by
  classical
  let e := Infinite.natEmbedding ι
  have hinv : ∀ n, Function.invFun e (e n) = n := Function.leftInverse_invFun e.injective
  have hval : ∀ s n, zfcFOn e s (e n) = zfcF (s ∘ e) n := fun s n => by
    simp [zfcFOn, hinv]
  refine ⟨zfcFOn e, fun s hs => zfcF_ne (s ∘ e) (funext fun n => ?_), fun s s' hne => ?_⟩
  · rw [← hval]; exact congrFun hs (e n)
  · by_cases heq : s ∘ e = s' ∘ e
    · obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      have hkr : k ∉ range e := by
        rintro ⟨n, rfl⟩; exact hk (congrFun heq n)
      exact ⟨k, hk, by simp [zfcFOn, hkr]⟩
    · obtain ⟨n, hn, hF⟩ := zfcF_exclusive _ _ heq
      exact ⟨e n, hn, by rw [hval, hval]; exact hF⟩

/-- **Any infinite party set (ZFC).** An exclusive process on infinitely many binary parties that
is not a process function. -/
theorem exists_exclusive_not_pf_of_infinite {ι : Type} [Infinite ι] :
    ∃ (I : ι → Type) (w : (ι → Bool) → (∀ k, I k)), Exclusive w ∧ ¬ IsProcessFunction w :=
  (exists_exclusive_not_pf_iff (fun _ : ι => Bool)).2 exists_exclusive_fixedPointFree_of_infinite

/-! ### The Yablo map -/

open Classical in
/-- Party `k` outputs "on" iff every later party is off. -/
noncomputable def yablo (s : ℕ → Bool) (k : ℕ) : Bool := decide (∀ j, k < j → s j = false)

theorem yablo_ne (s : ℕ → Bool) : yablo s ≠ s := by
  intro h
  by_cases hs : ∃ k, s k = true
  · obtain ⟨k, hk⟩ := hs
    have hall : ∀ j, k < j → s j = false := by
      have := congrFun h k; rw [hk] at this; simpa [yablo] using this
    have h1 := congrFun h (k + 1)
    rw [hall (k + 1) (by omega)] at h1
    simp only [yablo, decide_eq_false_iff_not] at h1
    exact h1 fun j hj => hall j (by omega)
  · have hs' : ∀ k, s k = false := fun k => by
      cases hk : s k
      · rfl
      · exact absurd ⟨k, hk⟩ hs
    have := congrFun h 0
    rw [hs' 0] at this
    simp only [yablo, decide_eq_false_iff_not] at this
    exact this fun j _ => hs' j

theorem yablo_not_exclusive : ¬ Exclusive yablo := by
  intro hex
  have hne : (fun _ : ℕ => false) ≠ fun _ => true := fun h => by simpa using congrFun h 0
  obtain ⟨k, -, hk⟩ := hex _ _ hne
  have h1 : yablo (fun _ => false) k = true := by simp [yablo]
  have h2 : yablo (fun _ => true) k = false := by
    simp only [yablo, decide_eq_false_iff_not]; exact fun h => by simpa using h (k + 1) (by omega)
  rw [h1, h2] at hk; exact Bool.noConfusion hk

/-- **Class 1.** Each coordinate of the Yablo map is a pointwise limit of continuous maps. -/
theorem yablo_coord_baireOne (k : ℕ) : BaireOne fun s => yablo s k := by
  classical
  refine ⟨fun M s => decide (∀ j ∈ Finset.Ioo k M, s j = false),
    fun M => continuous_of_finset_dep (Finset.Ioo k M) fun x y hxy => ?_, fun s => ?_⟩
  · simp only [decide_eq_decide]
    exact forall₂_congr fun j hj => by rw [hxy j hj]
  · apply tendsto_bool_of_eventually
    by_cases hs : ∀ j, k < j → s j = false
    · exact Eventually.of_forall fun M => by
        simp only [yablo, decide_eq_decide]
        exact ⟨fun _ j hj => hs j hj, fun _ j hj => hs j (Finset.mem_Ioo.1 hj).1⟩
    · push Not at hs
      obtain ⟨j, hj, hsj⟩ := hs
      filter_upwards [eventually_gt_atTop j] with M hM
      simp only [yablo, decide_eq_decide]
      constructor
      · intro h; simpa [hsj] using h j (Finset.mem_Ioo.2 ⟨hj, hM⟩)
      · intro h; simpa [hsj] using h j hj

theorem yablo_baireOne : BaireOne yablo := by
  classical
  choose g hg hlim using yablo_coord_baireOne
  refine ⟨fun M s k => g k M s, fun M => continuous_pi fun k => hg k M, fun s => ?_⟩
  rw [tendsto_pi_nhds]; exact fun k => hlim k s

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_continuousAt_of_baireOne
#print axioms PFUL.Infinite.finSupp_isFσ
#print axioms PFUL.Infinite.zfcF_measurable
#print axioms PFUL.Infinite.zfcF_borel_measurable
#print axioms PFUL.Infinite.zfcF_coord_baireTwo
#print axioms PFUL.Infinite.zfcF_coord0_not_baireOne
#print axioms PFUL.Infinite.zfcF_not_baireOne
#print axioms PFUL.Infinite.exists_subcube_fixed
#print axioms PFUL.Infinite.exists_fixed_of_finite_discontinuities
#print axioms PFUL.Infinite.exists_fixed_of_piece_constant
#print axioms PFUL.Infinite.exists_exclusive_not_pf_of_infinite
#print axioms PFUL.Infinite.yablo_ne
#print axioms PFUL.Infinite.yablo_not_exclusive
#print axioms PFUL.Infinite.yablo_baireOne
