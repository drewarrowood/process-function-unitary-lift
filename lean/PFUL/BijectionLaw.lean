/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Replacing the group law by a free family of bijections

The induced closed loop is evaluated at `σ k (w f k) (e k)` instead of `w f k + e k`, where
`σ k : I k → Equiv.Perm (I k)` is an arbitrary family of bijections of the input alphabet
(the group case is `σ k a = Equiv.addLeft a`). Arbitrary discrete alphabets, finitely many parties.

* PF ⇒ unitary (`induced_unitary_l2_σ`): **no condition on σ** (each `σ k a` is a bijection).
* copy gadget, unitary for all local kernels ⇒ PF (`unitary_l2_iff_pf_σ`): `σ` **free**
  (`σ a c = σ a' c → a = a'`); no structure on the output alphabets (the gadget uses
  `Equiv.swap`), which need only be nonempty.
* no ancillas (`unitary_l2_noAncilla_iff_pf_σ`): `σ` free and `e k : O k ≃ I k`.
Simply transitive actions (and group shifts) are free; transitivity is not needed.
-/
import PFUL.GeneralAlphabets

open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace PFUL.General
open PFUL.Countable

/-- A family of bijections acts freely: distinct labels move every point differently. -/
def Free {B : Type*} (σ : B → Equiv.Perm B) : Prop := ∀ a a' c, σ a c = σ a' c → a = a'

lemma free_addLeft {B : Type*} [AddCommGroup B] : Free (fun a : B => Equiv.addLeft a) :=
  fun a a' c h => by simpa using h

lemma shift_summableσ {I' X' : Type*} (τ : Equiv.Perm I') (v : I' × X' → ℂ)
    (hv : Summable fun c => ‖v c‖ ^ 2) :
    Summable fun p : I' × X' => ‖v (τ p.1, p.2)‖ ^ 2 :=
  ((τ.prodCongr (Equiv.refl X')).summable_iff (f := fun c => ‖v c‖ ^ 2)).2 hv

lemma shift_hasSumσ {I' X' : Type*} (v u : I' × X' → ℂ) (a : ℂ)
    (h : HasSum (fun c => v c * star (u c)) a) (τ : Equiv.Perm I') :
    HasSum (fun p : I' × X' => v (τ p.1, p.2) * star (u (τ p.1, p.2))) a :=
  ((τ.prodCongr (Equiv.refl X')).hasSum_iff (f := fun c => v c * star (u c))).2 h

section Witness
variable {O B : Type*} [DecidableEq O] [DecidableEq B]

lemma local_witnessσ (σ : B → Equiv.Perm B) (hσ : Free σ) (e : O ≃ B) (x x' : O) (a a' : B)
    (h : x ≠ x' → a ≠ a') :
    ∃ V : O × Unit → B × Unit → ℂ,
      (∀ u, Summable fun c => ‖V u c‖ ^ 2) ∧
      (∀ u v, HasSum (fun c => V u c * star (V v c)) (if u = v then 1 else 0)) ∧
      (∀ c, ∑' r, ((‖V r c‖₊ : ℝ≥0∞)) ^ 2 = 1) ∧
      ∑' c : B × Unit, V (x, ()) (σ a c.1, c.2) * star (V (x', ()) (σ a' c.1, c.2)) ≠ 0 := by
  by_cases hA : x = x' ∧ a ≠ a'
  · obtain ⟨rfl, haa⟩ := hA
    set p := e x
    set c0 := (σ a').symm p
    set q := σ a c0
    have hqp : q ≠ p := by
      intro hq; exact haa (hσ a a' c0 (hq.trans ((σ a').apply_symm_apply p).symm))
    refine ⟨liftK (rot p q) e, (liftK_good (good_rot (Ne.symm hqp)) e).1,
      (liftK_good (good_rot (Ne.symm hqp)) e).2.1, (liftK_good (good_rot (Ne.symm hqp)) e).2.2, ?_⟩
    set F : B → ℝ := fun i => rot p q p (σ a i) * rot p q p (σ a' i)
    have hF : ∀ i, 0 ≤ F i := fun i => mul_nonneg (row_p_nonneg _ _ _) (row_p_nonneg _ _ _)
    have hsum : Summable F := by
      have h1 := ((σ a).summable_iff (f := fun j => (rot p q p j) ^ 2)).2
        (rot_sq_real (Ne.symm hqp) p).summable
      have h2 := ((σ a').summable_iff (f := fun j => (rot p q p j) ^ 2)).2
        (rot_sq_real (Ne.symm hqp) p).summable
      refine Summable.of_nonneg_of_le hF (fun i => ?_) (h1.add h2)
      simp only [F, Function.comp]
      nlinarith [sq_nonneg (rot p q p (σ a i) - rot p q p (σ a' i))]
    have hpos : 0 < ∑' i, F i := by
      refine Summable.tsum_pos hsum hF c0 ?_
      have e1 : σ a' c0 = p := by simp [c0]
      show 0 < rot p q p (σ a c0) * rot p q p (σ a' c0)
      rw [e1, show σ a c0 = q from rfl]
      simp only [rot, if_neg hqp, if_pos rfl]
      norm_num
    have : ∑' c : B × Unit, liftK (rot p q) e (x, ()) (σ a c.1, c.2) *
        star (liftK (rot p q) e (x, ()) (σ a' c.1, c.2)) = ((∑' i, F i : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum, ← (Equiv.prodPUnit B).tsum_eq]
      congr 1; funext c
      simp [liftK, F, p]
    rw [this]
    exact_mod_cast hpos.ne'
  · set t := σ a' ((σ a).symm (e x))
    set τ : O ≃ B := e.trans (Equiv.swap (e x') t)
    have hτx' : τ x' = t := by simp [τ]
    have hτx : τ x = e x := by
      by_cases hx : x = x'
      · subst hx
        have : a = a' := by by_contra h'; exact hA ⟨rfl, h'⟩
        subst this
        simp [τ, t]
      · have haa := h hx
        simp only [τ, Equiv.trans_apply]
        refine Equiv.swap_apply_of_ne_of_ne (fun h' => hx (e.injective h')) (fun h' => ?_)
        apply haa
        apply hσ a a' ((σ a).symm (e x))
        simp only [Equiv.apply_symm_apply]
        exact h'
    refine ⟨liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ, (liftK_good good_id τ).1,
      (liftK_good good_id τ).2.1, (liftK_good good_id τ).2.2, ?_⟩
    have : ∑' c : B × Unit, liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ (x, ()) (σ a c.1, c.2) *
        star (liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ (x', ()) (σ a' c.1, c.2))
        = ∑' i : B, if i = (σ a).symm (e x) then (1:ℂ) else 0 := by
      rw [← (Equiv.prodPUnit B).tsum_eq]
      congr 1; funext c
      simp only [liftK, Equiv.prodPUnit_apply]
      have k1 : (σ a c.1 = τ x) ↔ c.1 = (σ a).symm (e x) := by
        rw [hτx, Equiv.eq_symm_apply]
      have k2 : (σ a' c.1 = τ x') ↔ c.1 = (σ a).symm (e x) := by
        rw [hτx']; exact (σ a').injective.eq_iff
      by_cases hc : c.1 = (σ a).symm (e x)
      · rw [if_pos (k1.2 hc), if_pos (k2.2 hc), if_pos hc]; simp
      · rw [if_neg (mt k1.1 hc), if_neg (mt k2.1 hc), if_neg hc]; simp
    rw [this, tsum_ite_eq]; exact one_ne_zero

end Witness

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*}
variable (σ : ∀ k, I k → Equiv.Perm (I k))

/-- Unit columns of the induced map, arbitrary alphabets. -/
theorem induced_colnorm_σ {X Y : ι → Type*} 
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hV : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) (e : ∀ k, I k) (x : ∀ k, X k) :
    ∑' r : (∀ k, O k) × (∀ k, Y k),
      ((‖∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (e k), x k)‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
  have : ∀ k, Nonempty (I k) := fun k => ⟨e k⟩
  simp_rw [nnnorm_prod, ENNReal.ofNNReal_finsetProd, ← Finset.prod_pow]
  exact tsum_prod_eq_one_anc_any w hw (fun k i z => ((‖V k z (σ k i (e k), x k)‖₊ : ℝ≥0∞)) ^ 2)
    (fun k i => hV k _)

theorem induced_rows_σ {X Y : ι → Type*} [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (r r' : (∀ k, O k) × (∀ k, Y k)) :
    HasSum (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (σ k (w r'.1 k) (c.1 k), c.2 k)))
      (if r = r' then 1 else 0) := by
  classical
  let g : ∀ k, I k × X k → ℂ := fun k p =>
    V k (r.1 k, r.2 k) (σ k (w r.1 k) p.1, p.2) * star (V k (r'.1 k, r'.2 k) (σ k (w r'.1 k) p.1, p.2))
  have hg : ∀ k, Summable fun p => ‖g k p‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_star_le _ _)
      ((shift_summableσ (σ k _) _ (hsq k _)).add (shift_summableσ (σ k _) _ (hsq k _)))
  have hp := hasSum_pi_prod_any g hg
  let e : ((∀ k, I k) × (∀ k, X k)) ≃ (∀ k, I k × X k) :=
    { toFun := fun c k => (c.1 k, c.2 k)
      invFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  have hp' := (e.hasSum_iff (f := fun x : (∀ k, I k × X k) => ∏ k, g k (x k))).2 hp
  have hfun : (fun c : (∀ k, I k) × (∀ k, X k) =>
        (∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (σ k (w r'.1 k) (c.1 k), c.2 k)))
      = (fun x : (∀ k, I k × X k) => ∏ k, g k (x k)) ∘ e := by
    funext c
    simp only [Function.comp, star_prod, ← Finset.prod_mul_distrib, g, e, Equiv.coe_fn_mk]
  rw [hfun]
  convert hp' using 1
  -- evaluate the product of the factor sums
  have hfac : ∀ k, w r.1 k = w r'.1 k →
      ∑' p, g k p = if (r.1 k, r.2 k) = (r'.1 k, r'.2 k) then 1 else 0 := by
    intro k hk
    have := shift_hasSumσ (V k (r.1 k, r.2 k)) (V k (r'.1 k, r'.2 k)) _
      (hrow k (r.1 k, r.2 k) (r'.1 k, r'.2 k)) (σ k (w r.1 k))
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

theorem induced_unitary_l2_σ {X Y : ι → Type*} [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (X k)]
    [∀ k, DecidableEq (O k)] [∀ k, DecidableEq (Y k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (V : ∀ k, O k × Y k → I k × X k → ℂ)
    (hsq : ∀ k a, Summable fun c => ‖V k a c‖ ^ 2)
    (hrow : ∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0))
    (hcol : ∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) :
    ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 ≃ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
      (∀ v r, HasSum (fun c => (∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) * v c) (Φ v r)) ∧
      ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k) := by
  classical
  set M : (∀ k, O k) × (∀ k, Y k) → (∀ k, I k) × (∀ k, X k) → ℂ :=
    fun r c => ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k) with hM
  have hR : ∀ r r', HasSum (fun c => M r c * star (M r' c)) (if r = r' then 1 else 0) :=
    fun r r' => induced_rows_σ σ w hw V hsq hrow r r'
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
      have hcn := induced_colnorm_σ σ w hw V hcol c.1 c.2
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
variable [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

/-- Copy gadget without any algebra on `O`: `(i, x) ↦ (swap x₀ (f i) x, i)`. -/
def gadgetσ (x0 : ∀ k, O k) (f : ∀ k, I k → O k) (k : ι) : O k × I k → I k × O k → ℂ :=
  fun r c => if r = (Equiv.swap (x0 k) (f k c.1) c.2, c.1) then 1 else 0

lemma gadgetσ_row (x0 : ∀ k, O k) (f : ∀ k, I k → O k) (k : ι) (r : O k × I k) :
    gadgetσ x0 f k r = fun c => if c = (r.2, Equiv.swap (x0 k) (f k r.2) r.1) then 1 else 0 := by
  funext c
  obtain ⟨o, y⟩ := r; obtain ⟨i, x⟩ := c
  simp only [gadgetσ, Prod.mk.injEq]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨rfl, by rw [h1, Equiv.swap_apply_self]⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨by rw [Equiv.swap_apply_self], rfl⟩

lemma gadgetσ_sq (x0 : ∀ k, O k) (f : ∀ k, I k → O k) (k : ι) (a : O k × I k) :
    Summable fun c => ‖gadgetσ x0 f k a c‖ ^ 2 := by
  rw [gadgetσ_row]
  refine (hasSum_ite_eq (a.2, Equiv.swap (x0 k) (f k a.2) a.1) (1 : ℝ)).summable.congr fun c => ?_
  split_ifs with h <;> simp [h]

lemma gadgetσ_rows (x0 : ∀ k, O k) (f : ∀ k, I k → O k) (k : ι) (a b : O k × I k) :
    HasSum (fun c => gadgetσ x0 f k a c * star (gadgetσ x0 f k b c)) (if a = b then 1 else 0) := by
  rw [gadgetσ_row, gadgetσ_row]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    convert hasSum_ite_eq (a.2, Equiv.swap (x0 k) (f k a.2) a.1) (1 : ℂ) using 1
    funext c; split_ifs <;> simp
  · simp only [hab, if_false]
    convert hasSum_zero (α := ℂ) (β := I k × O k) using 1
    funext c
    by_cases h1 : c = (a.2, Equiv.swap (x0 k) (f k a.2) a.1)
    · have h2 : c ≠ (b.2, Equiv.swap (x0 k) (f k b.2) b.1) := by
        rintro rfl
        apply hab
        obtain ⟨o, y⟩ := a; obtain ⟨o', y'⟩ := b
        simp only [Prod.mk.injEq] at h1
        obtain ⟨rfl, h⟩ := h1
        exact Prod.ext ((Equiv.swap _ _).injective h.symm) rfl
      rw [if_pos h1, if_neg h2]; simp
    · simp [h1]

lemma gadgetσ_col (x0 : ∀ k, O k) (f : ∀ k, I k → O k) (k : ι) (c : I k × O k) :
    ∑' r, ((‖gadgetσ x0 f k r c‖₊ : ENNReal)) ^ 2 = 1 := by
  have : (fun r => ((‖gadgetσ x0 f k r c‖₊ : ENNReal)) ^ 2)
      = fun r => if r = (Equiv.swap (x0 k) (f k c.1) c.2, c.1) then 1 else 0 := by
    funext r; simp only [gadgetσ]; split_ifs <;> simp
  rw [this, tsum_ite_eq]

/-- An isometric realisation of the σ-gadget for `f` forces a unique fixed point of
`g k i = f k (σ k i (e k))`. -/
theorem existsUnique_of_isometry_σ (w : (∀ k, O k) → (∀ k, I k)) (x0 : ∀ k, O k) (e : ∀ k, I k)
    (f : ∀ k, I k → O k)
    (Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
        lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2)
    (hΦ : ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
      = ∏ k, gadgetσ x0 f k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) :
    ∃! s : ∀ k, O k, ∀ k, f k (σ k (w s k) (e k)) = s k := by
  classical
  set v := Φ (lp.single 2 ((e, x0) : (∀ k, I k) × (∀ k, O k)) (1 : ℂ))
  set P : (∀ k, O k) × (∀ k, I k) → Prop := fun r =>
    (∀ k, f k (σ k (w r.1 k) (e k)) = r.1 k) ∧ r.2 = fun k => σ k (w r.1 k) (e k)
  have hcol : ∀ r, (∏ k, gadgetσ x0 f k (r.1 k, r.2 k) (σ k (w r.1 k) (e k), x0 k))
      = if P r then 1 else 0 := by
    intro r
    simp only [gadgetσ, Equiv.swap_apply_left, Prod.mk.injEq]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies, P]
    constructor
    · intro h; exact ⟨fun k => (h k).1.symm, funext fun k => (h k).2⟩
    · rintro ⟨h1, h2⟩ k; exact ⟨(h1 k).symm, congrFun h2 k⟩
  have hv : ∀ r, ‖v r‖ ^ 2 = if P r then 1 else 0 := by
    intro r
    simp only [v, hΦ]
    rw [hcol]
    split_ifs <;> simp
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hnorm : ‖v‖ = 1 := by
    simp only [v, Φ.norm_map, lp.norm_single (p := 2) (by norm_num)]; simp
  have hsum := lp.norm_rpow_eq_tsum hp v
  have hsumm : Summable fun r => ‖v r‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp v).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hnorm, one_pow] at hsum hsumm
  simp_rw [hv] at hsum hsumm
  have hex : ∃ r, P r := by
    by_contra h
    push Not at h
    simp [h] at hsum
  obtain ⟨r0, hr0⟩ := hex
  refine ⟨r0.1, hr0.1, fun s hs => ?_⟩
  by_contra hne
  let a : (∀ k, O k) × (∀ k, I k) := (s, fun k => σ k (w s k) (e k))
  have hPa : P a := ⟨hs, rfl⟩
  have hab : a ≠ r0 := fun h => hne (by rw [← h])
  have hle := hsumm.sum_le_tsum ({a, r0} : Finset _) (fun r _ => by split_ifs <;> norm_num)
  rw [Finset.sum_pair hab, if_pos hPa, if_pos hr0, ← hsum] at hle
  norm_num at hle

/-- **Copy-gadget converse with a free family of bijections.** -/
theorem not_isometry_of_not_pf_σ (hσ : ∀ k, Free (σ k)) [∀ k, Nonempty (O k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : ¬ IsProcessFunction w) :
    ∃ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) ∧
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) ∧
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) ∧
      ¬ ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 →ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k) := by
  classical
  unfold IsProcessFunction at hw
  push Not at hw
  obtain ⟨f0, hf⟩ := hw
  let x0 : ∀ k, O k := fun k => Classical.arbitrary _
  let s0 : ∀ k, O k := x0
  let e : ∀ k, I k := fun k => w s0 k
  -- realise f0 as i ↦ f (σ i e) (σ free ⇒ i ↦ σ i e injective)
  let f : ∀ k, I k → O k := fun k j =>
    if h : ∃ i, σ k i (e k) = j then f0 k h.choose else x0 k
  have hf' : ∀ k i, f k (σ k i (e k)) = f0 k i := by
    intro k i
    have h : ∃ i', σ k i' (e k) = σ k i (e k) := ⟨i, rfl⟩
    simp only [f, dif_pos h]
    rw [hσ k _ _ _ h.choose_spec]
  refine ⟨gadgetσ x0 f, gadgetσ_sq x0 f, gadgetσ_rows x0 f, gadgetσ_col x0 f, ?_⟩
  rintro ⟨Φ, hΦ⟩
  obtain ⟨s, hs, hu⟩ := existsUnique_of_isometry_σ σ w x0 e f Φ hΦ
  exact hf ⟨s, fun k => by rw [← hf' k]; exact hs k,
    fun t ht => hu t fun k => by rw [hf' k]; exact ht k⟩

/-- **Theorem 1.2 with a free family of bijections in place of the group law**, arbitrary
discrete alphabets, ancillas `X = O`, `Y = I`. -/
theorem unitary_l2_iff_pf_σ (hσ : ∀ k, Free (σ k)) [∀ k, Nonempty (O k)]
    (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, O k × I k → I k × O k → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ENNReal)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ k, O k) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, I k) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k))
    ↔ IsProcessFunction w := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨V, h1, h2, h3, hno⟩ := not_isometry_of_not_pf_σ σ hσ w hw
    obtain ⟨Φ, hΦ⟩ := h V h1 h2 h3
    exact hno ⟨Φ.toLinearIsometry, hΦ⟩
  · intro hw V h1 h2 h3
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2_σ σ w hw V h1 h2 h3
    exact ⟨Φ, hΦ⟩

end Gadget


section NoAnc
variable (hσ : ∀ k, Free (σ k)) [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

theorem exclusive_of_unitary_l2_σ (hσ : ∀ k, Free (σ k)) (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k))
    (h : ∀ V : ∀ k, O k × Unit → I k × Unit → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ _ : ι, Unit) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ _ : ι, Unit) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) :
    FiniteBox.Exclusive w := by
  classical
  intro s s' hne
  by_contra hno
  push Not at hno
  have hW : ∀ k, ∃ V : O k × Unit → I k × Unit → ℂ,
      (∀ u, Summable fun c => ‖V u c‖ ^ 2) ∧
      (∀ u v, HasSum (fun c => V u c * star (V v c)) (if u = v then 1 else 0)) ∧
      (∀ c, ∑' r, ((‖V r c‖₊ : ℝ≥0∞)) ^ 2 = 1) ∧
      ∑' c : I k × Unit, V (s k, ()) (σ k (w s k) c.1, c.2) * star (V (s' k, ()) (σ k (w s' k) c.1, c.2)) ≠ 0 :=
    fun k => local_witnessσ (σ k) (hσ k) (e k) (s k) (s' k) (w s k) (w s' k) (hno k)
  choose V hsq hrow hcol hnz using hW
  obtain ⟨Φ, hΦ⟩ := h V hsq hrow hcol
  let r : (∀ k, O k) × (∀ _ : ι, Unit) := (s, fun _ => Unit.unit)
  let r' : (∀ k, O k) × (∀ _ : ι, Unit) := (s', fun _ => Unit.unit)
  have hrr : r ≠ r' := fun h' => hne (congrArg Prod.fst h')
  have h0 := rows_of_lie Φ _ hΦ r r'
  rw [if_neg hrr] at h0
  let g : ∀ k, I k × Unit → ℂ := fun k p =>
    V k (s k, ()) (σ k (w s k) p.1, p.2) * star (V k (s' k, ()) (σ k (w s' k) p.1, p.2))
  have hg : ∀ k, Summable fun p => ‖g k p‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_star_le _ _)
      ((shift_summableσ (σ k _) _ (hsq k _)).add (shift_summableσ (σ k _) _ (hsq k _)))
  have hp := hasSum_pi_prod_any g hg
  let eq : ((∀ k, I k) × (∀ _ : ι, Unit)) ≃ (∀ k, I k × Unit) :=
    { toFun := fun c k => (c.1 k, c.2 k)
      invFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  have hp' := (eq.hasSum_iff (f := fun x : (∀ k, I k × Unit) => ∏ k, g k (x k))).2 hp
  have hfun : (fun c : (∀ k, I k) × (∀ _ : ι, Unit) =>
        (∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k)) *
          star (∏ k, V k (r'.1 k, r'.2 k) (σ k (w r'.1 k) (c.1 k), c.2 k)))
      = (fun x : (∀ k, I k × Unit) => ∏ k, g k (x k)) ∘ eq := by
    funext c
    simp only [Function.comp, star_prod, ← Finset.prod_mul_distrib, g, eq, Equiv.coe_fn_mk, r, r']
  rw [hfun] at h0
  have hz := h0.unique hp'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hz.symm
  exact hnz k hk

theorem unitary_l2_noAncilla_iff_pf_σ (hσ : ∀ k, Free (σ k)) [∀ k, Nonempty (O k)] (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k)) :
    (∀ V : ∀ k, O k × Unit → I k × Unit → ℂ,
      (∀ k a, Summable fun c => ‖V k a c‖ ^ 2) →
      (∀ k a b, HasSum (fun c => V k a c * star (V k b c)) (if a = b then 1 else 0)) →
      (∀ k c, ∑' r, ((‖V k r c‖₊ : ℝ≥0∞)) ^ 2 = 1) →
      ∃ Φ : lp (fun _ : (∀ k, I k) × (∀ _ : ι, Unit) => ℂ) 2 ≃ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ _ : ι, Unit) => ℂ) 2,
        ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r
          = ∏ k, V k (r.1 k, r.2 k) (σ k (w r.1 k) (c.1 k), c.2 k))
    ↔ IsProcessFunction w := by
  constructor
  · intro h f
    exact FiniteBox.existsUnique_of_exclusive w (exclusive_of_unitary_l2_σ σ hσ e w h) f
  · intro hw V hsq hrow hcol
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2_σ σ w hw V hsq hrow hcol
    exact ⟨Φ, hΦ⟩

end NoAnc

end PFUL.General

#print axioms PFUL.General.induced_unitary_l2_σ
#print axioms PFUL.General.unitary_l2_iff_pf_σ
#print axioms PFUL.General.exclusive_of_unitary_l2_σ
#print axioms PFUL.General.unitary_l2_noAncilla_iff_pf_σ
