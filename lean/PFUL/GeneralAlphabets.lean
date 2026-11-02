/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Arbitrary (possibly uncountable) discrete alphabets

Finitely many parties. No countability is assumed on any alphabet; `ℓ²(T)` is Mathlib's
`lp (fun _ : T => ℂ) 2` for an arbitrary type `T` (orthonormal basis `lp.single`).

* `exclusive_iff_pf` (purely combinatorial): for finitely many parties and nonempty output
  alphabets of arbitrary types, pairwise exclusivity ⇔ every deterministic intervention has
  exactly one fixed point. `exclusive_not_pf_of_empty` shows `Nonempty (O k)` cannot be dropped.
* `hasSum_pi_prod_any`: factorisation of absolutely summable sums over a finite product, by
  reduction to the (countable) supports.
* `tsum_prod_eq_one_anc_any`: the column identity for arbitrary alphabets, by restricting to a
  countable box closed under the supports of the local probability vectors (a countable
  closure argument) and applying the countable theorem.
* `induced_unitary_l2_any`, `unitary_l2_iff_pf_any` (copy gadget, ancillas `X = O`, `Y = I`),
  `exclusive_of_unitary_l2_any`, `unitary_l2_noAncilla_iff_pf_any` (no ancillas, `O k ≃ I k`):
  the countable results with every `Countable` hypothesis removed. The abelian-group law on the
  alphabets is still in the statements (the kernels are evaluated at `w f k + e k`).
-/
import PFUL.NoAncillaL2

open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace PFUL.General
open PFUL.Countable

section Comb
variable {ι : Type*} {I O : ι → Type*}

/-- **Exclusivity ⇔ process function**, finitely many parties (`Finite ι`), arbitrary nonempty
output alphabets and arbitrary input alphabets; no decidability, finiteness, countability or
algebraic structure on any alphabet. -/
theorem exclusive_iff_pf [Finite ι] [∀ k, Nonempty (O k)] (w : (∀ k, O k) → (∀ k, I k)) :
    FiniteBox.Exclusive w ↔ ∀ f : ∀ k, I k → O k, ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  cases nonempty_fintype ι
  constructor
  · intro h f; exact FiniteBox.existsUnique_of_exclusive w h f
  · intro h s s' hne; exact exclusivity w h hne

/-- `Nonempty (O k)` is needed: one party with empty alphabets is (vacuously) exclusive but the
unique intervention has no fixed point. -/
theorem exclusive_not_pf_of_empty :
    FiniteBox.Exclusive (I := fun _ : Unit => Empty) (O := fun _ : Unit => Empty) (fun s => s) ∧
    ¬ ∀ f : ∀ _ : Unit, Empty → Empty, ∃! s : ∀ _ : Unit, Empty, ∀ k, f k (s k) = s k := by
  refine ⟨fun s => (s ()).elim, fun h => ?_⟩
  obtain ⟨s, -, -⟩ := h (fun _ e => e)
  exact (s ()).elim

end Comb

theorem hasSum_pi_prod_any {K : Type*} [Fintype K] {X : K → Type*}
    (g : ∀ k, X k → ℂ) (hg : ∀ k, Summable fun x => ‖g k x‖) :
    HasSum (fun x : (∀ k, X k) => ∏ k, g k (x k)) (∏ k, ∑' x, g k x) := by
  classical
  let S : ∀ k, Set (X k) := fun k => Function.support (g k)
  have hS : ∀ k, (S k).Countable := fun k => by
    have := (hg k).countable_support
    simpa [S, Function.support] using this
  have : ∀ k, Countable (S k) := fun k => (hS k).to_subtype
  let g' : ∀ k, S k → ℂ := fun k x => g k x.1
  have hg' : ∀ k, Summable fun x => ‖g' k x‖ := fun k => (hg k).subtype _
  have h1 := PFUL.Countable.hasSum_pi_prod g' hg'
  have ht : ∀ k, ∑' x, g' k x = ∑' x, g k x := fun k =>
    tsum_subtype_eq_of_support_subset (s := S k) (f := g k) subset_rfl
  simp_rw [ht] at h1
  let T : Set (∀ k, X k) := {x | ∀ k, x k ∈ S k}
  have hsupp : Function.support (fun x : (∀ k, X k) => ∏ k, g k (x k)) ⊆ T := by
    intro x hx k
    simp only [Function.mem_support] at hx
    exact Finset.prod_ne_zero_iff.1 hx k (Finset.mem_univ _)
  rw [← hasSum_subtype_iff_of_support_subset hsupp]
  let e : T ≃ ∀ k, S k := Equiv.subtypePiEquivPi
  have h2 := (e.hasSum_iff (f := fun x : (∀ k, S k) => ∏ k, g' k (x k))).2 h1
  exact h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O Y : ι → Type*}

section Closure
variable (w : (∀ k, O k) → (∀ k, I k)) (p : ∀ k, I k → O k × Y k → ℝ≥0∞)

/-- One closure step: add the supports of all `p k (w s k)` with `s` in the current box. -/
def step (C : ∀ k, Set (O k × Y k)) : ∀ k, Set (O k × Y k) := fun k =>
  C k ∪ ⋃ s ∈ {s : ∀ j, O j | ∀ j, s j ∈ Prod.fst '' C j}, Function.support (p k (w s k))

def cl (C : ∀ k, Set (O k × Y k)) : ∀ k, Set (O k × Y k) := fun k => ⋃ n, (step w p)^[n] C k

variable {w p}

lemma step_countable (hp : ∀ k i, ∑' z, p k i z = 1) {C : ∀ k, Set (O k × Y k)}
    (hC : ∀ k, (C k).Countable) (k : ι) : (step w p C k).Countable := by
  refine (hC k).union (Set.Countable.biUnion (Set.countable_pi fun j => (hC j).image _) fun s _ => ?_)
  exact Summable.countable_support_ennreal (by rw [hp]; exact ENNReal.one_ne_top)

lemma iter_countable (hp : ∀ k i, ∑' z, p k i z = 1) {C : ∀ k, Set (O k × Y k)}
    (hC : ∀ k, (C k).Countable) (n : ℕ) : ∀ k, ((step w p)^[n] C k).Countable := by
  induction n with
  | zero => exact hC
  | succ n ih => rw [Function.iterate_succ_apply']; exact step_countable hp ih

lemma cl_countable (hp : ∀ k i, ∑' z, p k i z = 1) {C : ∀ k, Set (O k × Y k)}
    (hC : ∀ k, (C k).Countable) (k : ι) : (cl w p C k).Countable :=
  Set.countable_iUnion fun n => iter_countable hp hC n k

lemma iter_mono (C : ∀ k, Set (O k × Y k)) : Monotone fun n => (step w p)^[n] C := by
  refine monotone_nat_of_le_succ fun n => ?_
  intro k
  rw [Function.iterate_succ_apply']
  exact Set.subset_union_left

lemma subset_cl (C : ∀ k, Set (O k × Y k)) (k : ι) : C k ⊆ cl w p C k :=
  fun z hz => Set.mem_iUnion.2 ⟨0, hz⟩

lemma cl_closed (C : ∀ k, Set (O k × Y k)) (s : ∀ j, O j)
    (hs : ∀ j, s j ∈ Prod.fst '' cl w p C j) (k : ι) :
    Function.support (p k (w s k)) ⊆ cl w p C k := by
  classical
  have : ∀ j, ∃ n, s j ∈ Prod.fst '' ((step w p)^[n] C j) := by
    intro j
    obtain ⟨z, hz, hzs⟩ := hs j
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hz
    exact ⟨n, z, hn, hzs⟩
  choose n hn using this
  set N := Finset.univ.sup n
  have hN : ∀ j, s j ∈ Prod.fst '' ((step w p)^[N] C j) := fun j =>
    Set.image_mono (iter_mono C (Finset.le_sup (Finset.mem_univ j)) j) (hn j)
  intro z hz
  refine Set.mem_iUnion.2 ⟨N + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr (Set.mem_biUnion (x := s) hN hz)

end Closure

/-- **Column identity, arbitrary alphabets.** -/
theorem tsum_prod_eq_one_anc_any [∀ k, Nonempty (I k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (p : ∀ k, I k → O k × Y k → ℝ≥0∞) (hp : ∀ k i, ∑' z, p k i z = 1) :
    ∑' r : (∀ k, O k) × (∀ k, Y k), ∏ k, p k (w r.1 k) (r.1 k, r.2 k) = 1 := by
  classical
  have hZ : ∀ k, Nonempty (O k × Y k) := by
    intro k
    by_contra h
    rw [not_nonempty_iff] at h
    have := hp k (Classical.arbitrary _)
    simp at this
  set F : (∀ k, O k) × (∀ k, Y k) → ℝ≥0∞ := fun r => ∏ k, p k (w r.1 k) (r.1 k, r.2 k)
  -- the key claim: for every countable nonempty seed, the sum over the closed box is 1
  have key : ∀ C0 : ∀ k, Set (O k × Y k), (∀ k, (C0 k).Countable) → (∀ k, (C0 k).Nonempty) →
      ∑' r : {r : (∀ k, O k) × (∀ k, Y k) |
        ∀ k, r.1 k ∈ Prod.fst '' cl w p C0 k ∧ r.2 k ∈ Prod.snd '' cl w p C0 k}, F r = 1 := by
    intro C0 hC0 hne
    set Cl := cl w p C0
    let A : ∀ k, Set (O k) := fun k => Prod.fst '' Cl k
    let B : ∀ k, Set (Y k) := fun k => Prod.snd '' Cl k
    have hA : ∀ k, Countable (A k) := fun k => ((cl_countable hp hC0 k).image _).to_subtype
    have hB : ∀ k, Countable (B k) := fun k => ((cl_countable hp hC0 k).image _).to_subtype
    have hAne : ∀ k, Nonempty (A k) := fun k =>
      let ⟨z, hz⟩ := hne k; ⟨⟨z.1, z, subset_cl C0 k hz, rfl⟩⟩
    let I' : ι → Type _ := fun k => {i : I k // ∃ s : ∀ j, A j, w (fun j => (s j).1) k = i}
    let w' : (∀ k, A k) → ∀ k, I' k := fun s k => ⟨w (fun j => (s j).1) k, s, rfl⟩
    have hw' : IsProcessFunction w' := by
      intro f'
      let f : ∀ k, I k → O k := fun k i =>
        if h : ∃ s : ∀ j, A j, w (fun j => (s j).1) k = i then (f' k ⟨i, h⟩).1
        else (Classical.arbitrary (A k)).1
      have hfA : ∀ k i, f k i ∈ A k := by
        intro k i; simp only [f]; split_ifs
        · exact (f' k _).2
        · exact (Classical.arbitrary (A k)).2
      have hf : ∀ (s : ∀ j, A j) k, f k (w (fun j => (s j).1) k) = (f' k (w' s k)).1 := by
        intro s k; simp only [f]; rw [dif_pos ⟨s, rfl⟩]
      obtain ⟨s, hs, hu⟩ := hw f
      let s' : ∀ k, A k := fun k => ⟨s k, by rw [← hs k]; exact hfA _ _⟩
      refine ⟨s', fun k => Subtype.ext ?_, fun t ht => funext fun k => Subtype.ext ?_⟩
      · rw [← hf]; exact hs k
      · have : (fun j => (t j).1) = s := hu _ (fun j => by rw [hf]; exact congrArg Subtype.val (ht j))
        exact congrFun this k
    let p' : ∀ k, I' k → A k × B k → ℝ≥0∞ := fun k i z => p k i.1 (z.1.1, z.2.1)
    have hp' : ∀ k i, ∑' z, p' k i z = 1 := by
      rintro k ⟨i, s, rfl⟩
      have hsupp : Function.support (p k (w (fun j => (s j).1) k)) ⊆
          {z | z.1 ∈ A k ∧ z.2 ∈ B k} := by
        intro z hz
        have := cl_closed C0 (fun j => (s j).1) (fun j => (s j).2) k hz
        exact ⟨⟨z, this, rfl⟩, ⟨z, this, rfl⟩⟩
      rw [← hp k (w (fun j => (s j).1) k), ← tsum_subtype_eq_of_support_subset hsupp]
      exact ((Equiv.Set.prod (A k) (B k)).tsum_eq
        (fun z : A k × B k => p k (w (fun j => (s j).1) k) (z.1.1, z.2.1))).symm
    have h := PFUL.Countable.tsum_prod_eq_one_anc w' hw' p' hp'
    rw [← h]
    let e : {r : (∀ k, O k) × (∀ k, Y k) | ∀ k, r.1 k ∈ A k ∧ r.2 k ∈ B k} ≃
        (∀ k, A k) × (∀ k, B k) :=
      { toFun := fun r => (fun k => ⟨r.1.1 k, (r.2 k).1⟩, fun k => ⟨r.1.2 k, (r.2 k).2⟩)
        invFun := fun q => ⟨(fun k => (q.1 k).1, fun k => (q.2 k).1), fun k => ⟨(q.1 k).2, (q.2 k).2⟩⟩
        left_inv := fun r => rfl
        right_inv := fun q => rfl }
    exact e.tsum_eq (fun q => ∏ k, p' k (w' q.1 k) (q.1 k, q.2 k))
  -- seed
  let z0 : ∀ k, O k × Y k := fun k => Classical.arbitrary _
  apply le_antisymm
  · refine ENNReal.summable.tsum_le_of_sum_le fun S => ?_
    let C0 : ∀ k, Set (O k × Y k) := fun k =>
      insert (z0 k) ((fun r : (∀ k, O k) × (∀ k, Y k) => (r.1 k, r.2 k)) '' (S : Set _))
    have hC0 : ∀ k, (C0 k).Countable := fun k =>
      ((S.finite_toSet.image _).insert _).countable
    have hmem : ∀ r ∈ S, ∀ k, r.1 k ∈ Prod.fst '' cl w p C0 k ∧ r.2 k ∈ Prod.snd '' cl w p C0 k := by
      intro r hr k
      have : (r.1 k, r.2 k) ∈ cl w p C0 k :=
        subset_cl C0 k (Set.mem_insert_of_mem _ ⟨r, hr, rfl⟩)
      exact ⟨⟨_, this, rfl⟩, ⟨_, this, rfl⟩⟩
    rw [← Finset.sum_subtype_of_mem F hmem, ← key C0 hC0 (fun k => ⟨z0 k, Set.mem_insert _ _⟩)]
    exact ENNReal.sum_le_tsum _
  · let C0 : ∀ k, Set (O k × Y k) := fun k => {z0 k}
    rw [← key C0 (fun k => Set.countable_singleton _) (fun k => Set.singleton_nonempty _)]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective F


/-- Unit columns of the induced map, arbitrary alphabets. -/
theorem induced_colnorm_any {X Y : ι → Type*} [∀ k, AddCommGroup (I k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hV : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) (e : ∀ k, I k) (x : ∀ k, X k) :
    ∑' r : (∀ k, O k) × (∀ k, Y k),
      ((‖∏ k, V k (r.1 k, r.2 k) (w r.1 k + e k, x k)‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
  have : ∀ k, Nonempty (I k) := fun k => ⟨e k⟩
  simp_rw [nnnorm_prod, ENNReal.ofNNReal_finsetProd, ← Finset.prod_pow]
  exact tsum_prod_eq_one_anc_any w hw (fun k i z => ((‖V k z (i + e k, x k)‖₊ : ℝ≥0∞)) ^ 2)
    (fun k i => hV k _)

theorem induced_rows_any {X Y : ι → Type*} [∀ k, AddCommGroup (I k)] [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (r r' : (∀ k, O k) × (∀ k, Y k)) :
    HasSum (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (w r'.1 k + c.1 k, c.2 k)))
      (if r = r' then 1 else 0) := by
  classical
  let g : ∀ k, I k × X k → ℂ := fun k p =>
    V k (r.1 k, r.2 k) (w r.1 k + p.1, p.2) * star (V k (r'.1 k, r'.2 k) (w r'.1 k + p.1, p.2))
  have hg : ∀ k, Summable fun p => ‖g k p‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_star_le _ _)
      ((shift_summable _ (hsq k _) _).add (shift_summable _ (hsq k _) _))
  have hp := hasSum_pi_prod_any g hg
  let e : ((∀ k, I k) × (∀ k, X k)) ≃ (∀ k, I k × X k) :=
    { toFun := fun c k => (c.1 k, c.2 k)
      invFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  have hp' := (e.hasSum_iff (f := fun x : (∀ k, I k × X k) => ∏ k, g k (x k))).2 hp
  have hfun : (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (w r'.1 k + c.1 k, c.2 k)))
      = (fun x : (∀ k, I k × X k) => ∏ k, g k (x k)) ∘ e := by
    funext c
    simp only [Function.comp, star_prod, ← Finset.prod_mul_distrib, g, e, Equiv.coe_fn_mk]
  rw [hfun]
  convert hp' using 1
  -- evaluate the product of the factor sums
  have hfac : ∀ k, w r.1 k = w r'.1 k →
      ∑' p, g k p = if (r.1 k, r.2 k) = (r'.1 k, r'.2 k) then 1 else 0 := by
    intro k hk
    have := shift_hasSum (V k (r.1 k, r.2 k)) (V k (r'.1 k, r'.2 k)) _
      (hrow k (r.1 k, r.2 k) (r'.1 k, r'.2 k)) (w r.1 k)
    simp only [g, ← hk]
    exact this.tsum_eq
  by_cases hrr : r = r'
  · subst hrr
    rw [ite_eq_left rfl]
    symm
    exact Finset.prod_eq_one (fun k _ => by rw [hfac k rfl, ite_eq_left rfl])
  · rw [ite_eq_right hrr]
    symm
    by_cases h1 : r.1 = r'.1
    · have h2 : r.2 ≠ r'.2 := fun h2 => hrr (Prod.ext h1 h2)
      obtain ⟨k, hk⟩ : ∃ k, r.2 k ≠ r'.2 k := by
        by_contra h; push Not at h; exact h2 (funext h)
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hfac k (by rw [h1]), ite_eq_right (fun h => hk (congrArg Prod.snd h))]
    · obtain ⟨k, hsk, hwk⟩ := exclusivity w hw h1
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hfac k hwk, ite_eq_right (fun h => hsk (congrArg Prod.fst h))]

theorem induced_unitary_l2_any {X Y : ι → Type*} [∀ k, AddCommGroup (I k)] [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (hcol : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 ≃ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      (∀ v r, HasSum (fun c => (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) * v c) (Φ v r)) ∧
      ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) := by
  classical
  set M : (∀ k, O k) × (∀ k, Y k) → (∀ k, I k) × (∀ k, X k) → ℂ :=
    fun r c => ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) with hM
  have hR : ∀ r r', HasSum (fun c => M r c * star (M r' c)) (if r = r' then 1 else 0) :=
    fun r r' => induced_rows_any w hw V hsq hrow r r'
  have hsq' : ∀ r, Summable fun c => ‖star (M r c)‖ ^ 2 := by
    intro r
    have h := (hR r r).summable
    have h2 : (fun c => M r c * star (M r c)) = fun c => ((‖M r c‖ ^ 2 : ℝ) : ℂ) := by
      funext c
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h2] at h
    simpa using Complex.summable_ofReal.1 h
  let u : (∀ k, O k) × (∀ k, Y k) → lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 := fun r =>
    ⟨fun c => star (M r c), memℓp_gen (by
      simpa [ENNReal.toReal_ofNat, Real.rpow_two] using hsq' r)⟩
  have hu_apply : ∀ r c, (u r : _ → ℂ) c = star (M r c) := fun r c => rfl
  have hinner : ∀ r (v : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2),
      HasSum (fun c => M r c * v c) ⟪u r, v⟫_ℂ := by
    intro r v
    have := lp.hasSum_inner (𝕜 := ℂ) (u r) v
    simpa [hu_apply, Complex.star_def, mul_comm] using this
  have hon : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro r r'
    have h1 := hinner r (u r')
    simp only [hu_apply] at h1
    exact h1.unique (hR r r')
  have hsp : (Submodule.span ℂ (Set.range u))ᗮ = ⊥ := by
    refine orthogonal_span_eq_bot u hon (fun c => lp.single 2 c (1 : ℂ)) ?_ ?_
    · intro x hx
      ext c
      have := hx c
      rw [lp.inner_single_left] at this
      simpa using this
    · intro c
      have hn : ‖(lp.single 2 c (1 : ℂ) : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2)‖ = 1 := by
        rw [lp.norm_single (by norm_num)]; simp
      rw [hn]
      have hcn := induced_colnorm_any w hw V hcol c.1 c.2
      have h := hasSum_real_of_ennreal (fun r => ‖M r c‖₊ ^ 2)
        (by simpa [ENNReal.coe_pow, hM] using hcn)
      have he : ∀ r, ⟪u r, (lp.single 2 c (1 : ℂ) : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2)⟫_ℂ = M r c := by
        intro r; rw [lp.inner_single_right]; simp [hu_apply, Complex.star_def]
      simpa [he] using h
  let B := HilbertBasis.mkOfOrthogonalEqBot hon hsp
  have hB : ∀ r, (B r : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2) = u r := fun r => by
    simp [B, HilbertBasis.coe_mkOfOrthogonalEqBot]
  refine ⟨B.repr, fun v r => ?_, fun r c => ?_⟩
  · rw [HilbertBasis.repr_apply_apply, hB]; exact hinner r v
  · rw [HilbertBasis.repr_apply_apply, hB, lp.inner_single_right]
    simp [hu_apply, hM]

section Gadget
variable [∀ k, AddCommGroup (I k)] [∀ k, AddCommGroup (O k)]
  [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

theorem existsUnique_of_isometry_l2_any (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, I k → O k)
    (Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2)
    (hΦ : ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
      = ∏ k, gadgetK f k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  set v := Φ (lp.single 2 (0 : (∀ k, I k) × (∀ k, O k)) (1 : ℂ))
  set P : (∀ k, O k) × (∀ k, I k) → Prop := fun r => (∀ k, f k (w r.1 k) = r.1 k) ∧ r.2 = w r.1
  have hv : ∀ r, ‖v r‖ ^ 2 = if P r then 1 else 0 := by
    intro r
    simp only [v, hΦ, Prod.fst_zero, Prod.snd_zero, induced_gadget_col0, P]
    split_ifs <;> simp
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hnorm : ‖v‖ = 1 := by
    simp only [v, Φ.norm_map, lp.norm_single (p := 2) (by norm_num)]; simp
  have hsum := lp.norm_rpow_eq_tsum hp v
  have hsumm : Summable fun r => ‖v r‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp v).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hnorm, one_pow] at hsum hsumm
  simp_rw [hv] at hsum hsumm
  -- existence
  have hex : ∃ r, P r := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨r0, hr0⟩ := hex
  refine ⟨r0.1, hr0.1, fun s hs => ?_⟩
  by_contra hne
  let a : (∀ k, O k) × (∀ k, I k) := (s, w s)
  have hPa : P a := ⟨hs, rfl⟩
  have hab : a ≠ r0 := fun h => hne (by rw [← h])
  have hle := hsumm.sum_le_tsum ({a, r0} : Finset _) (fun r _ => by split_ifs <;> norm_num)
  rw [Finset.sum_pair hab, if_pos hPa, if_pos hr0, ← hsum] at hle
  norm_num at hle

theorem not_isometry_of_not_pf_l2_any (w : (∀ k, O k) → (∀ k, I k)) (hw : ¬ IsProcessFunction w) :
    ∃ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) ∧
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) ∧
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) ∧
      ¬ ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k) := by
  unfold IsProcessFunction at hw
  push Not at hw
  obtain ⟨f, hf⟩ := hw
  refine ⟨gadgetK f, gadgetK_sq f, gadgetK_rows f, gadgetK_col f, ?_⟩
  rintro ⟨Φ, hΦ⟩
  obtain ⟨s, hs, hu⟩ := existsUnique_of_isometry_l2_any w f Φ hΦ
  exact hf ⟨s, hs, hu⟩

theorem unitary_l2_iff_pf_any (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))
    ↔ IsProcessFunction w := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨V, h1, h2, h3, hno⟩ := not_isometry_of_not_pf_l2_any w hw
    obtain ⟨Φ, hΦ⟩ := h V h1 h2 h3
    exact hno ⟨Φ.toLinearIsometry, hΦ⟩
  · intro hw V h1 h2 h3
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2_any w hw V h1 h2 h3
    exact ⟨Φ, hΦ⟩

end Gadget

section NoAnc
variable [∀ k, AddCommGroup (I k)] [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

theorem exclusive_of_unitary_l2_any (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k))
    (h : ∀ V : ∀ k, O k × Unit → I k × Unit → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ _ : ι, Unit) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ _ : ι, Unit) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) :
    FiniteBox.Exclusive w := by
  classical
  intro s s' hne
  by_contra hno
  push Not at hno
  have hW : ∀ k, ∃ V : O k × Unit → I k × Unit → ℂ,
      (∀ u, Summable fun c => ‖V u c‖ ^ 2) ∧
      (∀ u v, HasSum (fun c => V u c * star (V v c)) (if u = v then 1 else 0)) ∧
      (∀ c, ∑' r, ((‖V r c‖₊ : ℝ≥0∞)) ^ 2 = 1) ∧
      ∑' c : I k × Unit, V (s k, ()) (w s k + c.1, c.2) * star (V (s' k, ()) (w s' k + c.1, c.2)) ≠ 0 :=
    fun k => local_witness (e k) (s k) (s' k) (w s k) (w s' k) (hno k)
  choose V hsq hrow hcol hnz using hW
  obtain ⟨Φ, hΦ⟩ := h V hsq hrow hcol
  let r : (∀ k, O k) × (∀ _ : ι, Unit) := (s, fun _ => Unit.unit)
  let r' : (∀ k, O k) × (∀ _ : ι, Unit) := (s', fun _ => Unit.unit)
  have hrr : r ≠ r' := fun h' => hne (congrArg Prod.fst h')
  have h0 := rows_of_lie Φ _ hΦ r r'
  rw [if_neg hrr] at h0
  let g : ∀ k, I k × Unit → ℂ := fun k p =>
    V k (s k, ()) (w s k + p.1, p.2) * star (V k (s' k, ()) (w s' k + p.1, p.2))
  have hg : ∀ k, Summable fun p => ‖g k p‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_star_le _ _)
      ((shift_summable _ (hsq k _) _).add (shift_summable _ (hsq k _) _))
  have hp := hasSum_pi_prod_any g hg
  let eq : ((∀ k, I k) × (∀ _ : ι, Unit)) ≃ (∀ k, I k × Unit) :=
    { toFun := fun c k => (c.1 k, c.2 k)
      invFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  have hp' := (eq.hasSum_iff (f := fun x : (∀ k, I k × Unit) => ∏ k, g k (x k))).2 hp
  have hfun : (fun c : (∀ k, I k) × (∀ _ : ι, Unit) =>
        (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (w r'.1 k + c.1 k, c.2 k)))
      = (fun x : (∀ k, I k × Unit) => ∏ k, g k (x k)) ∘ eq := by
    funext c
    simp only [Function.comp, star_prod, ← Finset.prod_mul_distrib, g, eq, Equiv.coe_fn_mk, r, r']
  rw [hfun] at h0
  have hz := h0.unique hp'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hz.symm
  exact hnz k hk

theorem unitary_l2_noAncilla_iff_pf_any (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, O k × Unit → I k × Unit → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ _ : ι, Unit) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ _ : ι, Unit) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))
    ↔ IsProcessFunction w := by
  constructor
  · intro h f
    have : ∀ k, Nonempty (O k) := fun k => ⟨(e k).symm 0⟩
    exact FiniteBox.existsUnique_of_exclusive w (exclusive_of_unitary_l2_any e w h) f
  · intro hw V hsq hrow hcol
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2_any w hw V hsq hrow hcol
    exact ⟨Φ, hΦ⟩

end NoAnc

/-- Sanity check: the theorems apply to uncountable alphabets, e.g. `ℝ` (discrete, ℓ²(ℝ²)). -/
noncomputable example (w : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Prop := by
  classical
  exact (unitary_l2_iff_pf_any (I := fun _ : Fin 2 => ℝ) (O := fun _ => ℝ) w).1 = (unitary_l2_iff_pf_any (I := fun _ : Fin 2 => ℝ) (O := fun _ => ℝ) w).1

end PFUL.General

#print axioms PFUL.General.exclusive_iff_pf
#print axioms PFUL.General.exclusive_not_pf_of_empty
#print axioms PFUL.General.hasSum_pi_prod_any
#print axioms PFUL.General.tsum_prod_eq_one_anc_any
#print axioms PFUL.General.induced_unitary_l2_any
#print axioms PFUL.General.unitary_l2_iff_pf_any
#print axioms PFUL.General.exclusive_of_unitary_l2_any
#print axioms PFUL.General.unitary_l2_noAncilla_iff_pf_any
