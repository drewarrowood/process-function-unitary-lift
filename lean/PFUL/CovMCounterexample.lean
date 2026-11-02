/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# A consistent counterexample: exclusive ⇏ PF for countably many binary parties

Under an explicit hypothesis `CovMEqC` (cov(M) = 𝔠: fewer than 𝔠 meagre subsets of `ℕ → Bool`
never cover it), there is an exclusive, fixed-point-free `F : (ℕ → Bool) → (ℕ → Bool)`, hence an
exclusive non-process function. No axioms are added; `CovMEqC` is a theorem hypothesis.

Construction: well-order `ℕ → Bool` in type `ord 𝔠` (every initial segment has size `< 𝔠`) and
define `F` by well-founded recursion. If `x` is finite-difference equivalent to an earlier `y`,
copy `F y`. Otherwise choose `z` outside the `< 𝔠` meagre forbidden sets
`{z | {k ∈ D | z k = b k} finite}` (`D` infinite), one per earlier point and one for `z ~ x`.
-/
import PFUL.InfiniteParties

open Cardinal Set Filter Topology

namespace PFUL.Infinite

/-- cov(M) = 𝔠 for the Cantor space, in Lean-friendly form. -/
def CovMEqC : Prop :=
  ∀ (ι : Type) (A : ι → Set (ℕ → Bool)), #ι < 𝔠 → (∀ i, IsMeagre (A i)) → ⋃ i, A i ≠ Set.univ

/-- Finite-difference equivalence. -/
def FinDiff (s t : ℕ → Bool) : Prop := {k | s k ≠ t k}.Finite

/-- The forbidden set: `z` agrees with `b` at only finitely many points of `D`. -/
def Forb (D : Set ℕ) (b : ℕ → Bool) : Set (ℕ → Bool) := {z | {k | k ∈ D ∧ z k = b k}.Finite}

theorem forb_isMeagre {D : Set ℕ} (hD : D.Infinite) (b : ℕ → Bool) : IsMeagre (Forb D b) := by
  classical
  let C : ℕ → Set (ℕ → Bool) := fun n => {z | ∀ k ∈ D, n ≤ k → z k ≠ b k}
  have hsub : Forb D b ⊆ ⋃ n, C n := by
    intro z hz
    obtain ⟨n, hn⟩ := (hz.bddAbove)
    refine mem_iUnion.2 ⟨n + 1, fun k hk hnk hzk => ?_⟩
    have := hn ⟨hk, hzk⟩; omega
  refine IsMeagre.mono hsub (isMeagre_iUnion fun n => IsNowhereDense.isMeagre ?_)
  have hcl : IsClosed (C n) := by
    simp only [C, setOf_forall]
    refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    have hc : Continuous fun p : ℕ → Bool => p k := continuous_apply k
    exact (isClosed_discrete {c : Bool | c ≠ b k}).preimage hc
  rw [hcl.isNowhereDense_iff, eq_empty_iff_forall_notMem]
  intro z hz
  -- pick points of D beyond any bound
  have hpick : ∀ m, ∃ k ∈ D, max n m ≤ k := fun m => by
    by_contra h; push_neg at h
    exact hD ((finite_lt_nat (max n m)).subset fun k hk => h k hk)
  choose kk hkD hkle using hpick
  let zs : ℕ → (ℕ → Bool) := fun m => Function.update z (kk m) (b (kk m))
  have hlim : Tendsto zs atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]; intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop j] with m hm
    have : j ≠ kk m := by have := hkle m; omega
    simp [zs, Function.update_of_ne this]
  obtain ⟨m, hm⟩ := (hlim.eventually (isOpen_interior.mem_nhds hz)).exists
  have := interior_subset hm (kk m) (hkD m) (le_trans (le_max_left _ _) (hkle m))
  simp [zs] at this

lemma finDiff_refl (s : ℕ → Bool) : FinDiff s s := by simp [FinDiff]
lemma finDiff_symm {s t : ℕ → Bool} (h : FinDiff s t) : FinDiff t s := by
  simpa [FinDiff, ne_comm] using h
lemma finDiff_trans {s t u : ℕ → Bool} (h : FinDiff s t) (h' : FinDiff t u) : FinDiff s u :=
  (h.union h').subset fun k hk => by
    by_contra hc; simp only [mem_union, mem_setOf_eq, not_or, not_not] at hc
    exact hk (hc.1.trans hc.2)

/-- `FinDiff z x` is the forbidden set with `D = univ`, `b = !x`. -/
lemma finDiff_eq_forb (x : ℕ → Bool) : {z | FinDiff z x} = Forb Set.univ (fun k => !x k) := by
  ext z
  have : {k | z k ≠ x k} = {k | z k = !x k} := by
    ext k; simp only [mem_setOf_eq]
    rcases Bool.eq_false_or_eq_true (z k) with h | h <;>
      rcases Bool.eq_false_or_eq_true (x k) with h' | h' <;> simp [h, h']
  simp only [FinDiff, Forb, mem_setOf_eq, mem_univ, true_and, this]

section Construction
variable (r : (ℕ → Bool) → (ℕ → Bool) → Prop) [IsWellOrder (ℕ → Bool) r]

/-- The agreement set of a pair. -/
def Agr (F : (ℕ → Bool) → (ℕ → Bool)) (x y : ℕ → Bool) : Set ℕ :=
  {k | x k ≠ y k ∧ F x k = F y k}

open Classical in
noncomputable def step (x : ℕ → Bool) (prev : ∀ y, r y x → (ℕ → Bool)) : ℕ → Bool :=
  if h : ∃ y, ∃ hy : r y x, FinDiff y x then prev h.choose h.choose_spec.choose
  else Classical.epsilon fun z => ¬ FinDiff z x ∧
    ∀ y (hy : r y x), {k | x k ≠ y k ∧ z k = prev y hy k}.Infinite

noncomputable def theF : (ℕ → Bool) → (ℕ → Bool) :=
  WellFounded.fix (IsWellOrder.wf : WellFounded r) (step r)

lemma theF_eq (x) : theF r x = step r x (fun y _ => theF r y) :=
  WellFounded.fix_eq (IsWellOrder.wf : WellFounded r) _ x

/-- The pair invariant. -/
def Good (F : (ℕ → Bool) → (ℕ → Bool)) (x y : ℕ → Bool) : Prop :=
  (FinDiff x y → F x = F y) ∧ (¬ FinDiff x y → (Agr F x y).Infinite)

lemma good_symm {F} {x y} (h : Good F x y) : Good F y x := by
  refine ⟨fun hf => (h.1 (finDiff_symm hf)).symm, fun hf => ?_⟩
  have := h.2 (fun h' => hf (finDiff_symm h'))
  simpa [Agr, ne_comm, eq_comm] using this

theorem invariant (hH : CovMEqC) (hcard : ∀ x, #{y // r y x} < 𝔠) (x : ℕ → Bool) :
    ¬ FinDiff (theF r x) x ∧ ∀ y, r y x → Good (theF r) x y := by
  classical
  induction x using (IsWellOrder.wf : WellFounded r).induction with
  | _ x IH =>
  have goodAll : ∀ y y', r y x → r y' x → Good (theF r) y y' := by
    intro y y' hy hy'
    rcases trichotomous_of r y y' with h | h | h
    · exact good_symm ((IH y' hy').2 y h)
    · subst h; exact ⟨fun _ => rfl, fun h => (h (finDiff_refl _)).elim⟩
    · exact (IH y hy).2 y' h
  by_cases hex : ∃ y, ∃ hy : r y x, FinDiff y x
  · have hFx : theF r x = theF r hex.choose := by
      rw [theF_eq]; simp only [step, dif_pos hex]
    set y0 := hex.choose
    have hy0 : r y0 x := hex.choose_spec.choose
    have hy0x : FinDiff y0 x := hex.choose_spec.choose_spec
    refine ⟨fun h => (IH y0 hy0).1 ?_, fun y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
    · rw [hFx] at h; exact finDiff_trans h (finDiff_symm hy0x)
    · rw [hFx]; exact (goodAll y0 y hy0 hy).1 (finDiff_trans hy0x hxy)
    · have hn : ¬ FinDiff y0 y := fun h => hxy (finDiff_trans (finDiff_symm hy0x) h)
      have hinf := (goodAll y0 y hy0 hy).2 hn
      refine (hinf.diff hy0x).mono fun k hk => ?_
      simp only [Agr, mem_diff, mem_setOf_eq, not_not] at hk ⊢
      refine ⟨by rw [← hk.2]; exact hk.1.1, by rw [hFx]; exact hk.1.2⟩
  · -- choose by cov(M) = 𝔠
    let ι := Option {y // r y x}
    let A : ι → Set (ℕ → Bool) := fun o => match o with
      | none => {z | FinDiff z x}
      | some y => Forb {k | x k ≠ y.1 k} (theF r y.1)
    have hι : #ι < 𝔠 := by
      simp only [ι, mk_option]
      exact add_lt_of_lt aleph0_le_continuum (hcard x) (one_lt_aleph0.trans_le aleph0_le_continuum)
    have hA : ∀ o, IsMeagre (A o) := by
      rintro (_ | ⟨y, hy⟩)
      · show IsMeagre {z | FinDiff z x}
        rw [finDiff_eq_forb]; exact forb_isMeagre infinite_univ _
      · refine forb_isMeagre (fun hfin => hex ⟨y, hy, finDiff_symm ?_⟩) _
        simpa [FinDiff] using hfin
    obtain ⟨z, hz⟩ : ∃ z, z ∉ ⋃ o, A o := by
      by_contra h; push_neg at h; exact hH ι A hι hA (eq_univ_of_forall h)
    simp only [mem_iUnion, not_exists] at hz
    have hP : ∃ z, ¬ FinDiff z x ∧
        ∀ y (hy : r y x), {k | x k ≠ y k ∧ z k = theF r y k}.Infinite :=
      ⟨z, hz none, fun y hy => by simpa [A, Forb] using hz (some ⟨y, hy⟩)⟩
    have hFx := Classical.epsilon_spec hP
    have heq : theF r x = Classical.epsilon fun z => ¬ FinDiff z x ∧
        ∀ y (hy : r y x), {k | x k ≠ y k ∧ z k = theF r y k}.Infinite := by
      rw [theF_eq]; simp only [step, dif_neg hex]
    rw [← heq] at hFx
    refine ⟨hFx.1, fun y hy => ⟨fun hxy => (hex ⟨y, hy, finDiff_symm hxy⟩).elim, fun _ => ?_⟩⟩
    exact hFx.2 y hy
end Construction

lemma mk_cantor : #(ℕ → Bool) = 𝔠 := by
  rw [← power_def, mk_bool, mk_nat, two_power_aleph0]

/-- **Main theorem.** Under cov(M) = 𝔠 there is an exclusive, fixed-point-free self-map of the
Cantor space `ℕ → Bool`. -/
theorem exists_exclusive_fixedPointFree_of_covM (hH : CovMEqC) :
    ∃ F : (ℕ → Bool) → (ℕ → Bool), (∀ s, F s ≠ s) ∧ Exclusive F := by
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq (ℕ → Bool)
  have hcard : ∀ x, #{y // r y x} < 𝔠 := fun x => by
    rw [← mk_cantor, ← Ordinal.card_typein]; exact Cardinal.card_typein_lt x hr
  have inv := invariant r hH hcard
  refine ⟨theF r, fun s hs => (inv s).1 (by rw [hs]; exact finDiff_refl s), ?_⟩
  intro s s' hne
  have hg : Good (theF r) s s' := by
    rcases trichotomous_of r s s' with h | h | h
    · exact good_symm ((inv s').2 s h)
    · exact (hne h).elim
    · exact (inv s).2 s' h
  by_cases hf : FinDiff s s'
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    exact ⟨k, hk, by rw [hg.1 hf]⟩
  · obtain ⟨k, hk⟩ := (hg.2 hf).nonempty
    exact ⟨k, hk.1, hk.2⟩

/-- **Corollary.** Under cov(M) = 𝔠 there is an exclusive process on countably many binary
parties that is not a process function. -/
theorem exists_exclusive_not_pf_of_covM (hH : CovMEqC) :
    ∃ (I : ℕ → Type) (w : (ℕ → Bool) → (∀ k, I k)), Exclusive w ∧ ¬ IsProcessFunction w :=
  (exists_exclusive_not_pf_iff (fun _ : ℕ => Bool)).2 (exists_exclusive_fixedPointFree_of_covM hH)

/-- CH implies the hypothesis: a union of countably many meagre sets is meagre, and the Cantor
space (compact Hausdorff, hence Baire) is not meagre. -/
theorem covMEqC_of_CH (hCH : (𝔠 : Cardinal.{0}) = ℵ₁) : CovMEqC := by
  intro ι A hι hA hU
  have : Countable ι := Cardinal.mk_le_aleph0_iff.1 (lt_aleph_one_iff.1 (hι.trans_eq hCH))
  have hm : IsMeagre (Set.univ : Set (ℕ → Bool)) := hU ▸ isMeagre_iUnion hA
  obtain ⟨x, hx⟩ := (dense_of_mem_residual hm).nonempty
  simp at hx

/-- **Corollary (CH).** -/
theorem exists_exclusive_not_pf_of_CH (hCH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ (I : ℕ → Type) (w : (ℕ → Bool) → (∀ k, I k)), Exclusive w ∧ ¬ IsProcessFunction w :=
  exists_exclusive_not_pf_of_covM (covMEqC_of_CH hCH)

end PFUL.Infinite

#print axioms PFUL.Infinite.forb_isMeagre
#print axioms PFUL.Infinite.exists_exclusive_fixedPointFree_of_covM
#print axioms PFUL.Infinite.exists_exclusive_not_pf_of_covM
#print axioms PFUL.Infinite.exists_exclusive_not_pf_of_CH
