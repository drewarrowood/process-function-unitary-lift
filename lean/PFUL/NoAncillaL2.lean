import PFUL.ExclusiveInduction
import PFUL.CopyGadgetL2

/-!
# Countable alphabets, no ancillas: unitary for all local unitaries ⇔ process function
-/

open scoped ENNReal NNReal

namespace PFUL.Countable

/-- Matrix elements of a unitary between `ℓ²` spaces have orthonormal rows. -/
lemma rows_of_lie {R C : Type*} [DecidableEq R] [DecidableEq C]
    (Φ : lp (fun _ : C => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : R => ℂ) 2) (M : R → C → ℂ)
    (hΦ : ∀ r c, Φ (lp.single 2 c (1 : ℂ)) r = M r c) (r r' : R) :
    HasSum (fun c => M r c * star (M r' c)) (if r = r' then 1 else 0) := by
  set u : R → lp (fun _ : C => ℂ) 2 := fun r => Φ.symm (lp.single 2 r (1 : ℂ))
  have hM : ∀ r c, M r c = star (u r c) := by
    intro r c
    rw [← hΦ]
    have h1 : (Φ (lp.single 2 c (1:ℂ))) r = inner ℂ (lp.single 2 r (1:ℂ)) (Φ (lp.single 2 c (1:ℂ))) := by
      rw [lp.inner_single_left]; simp
    rw [h1]
    have h2 : lp.single 2 r (1:ℂ) = Φ (u r) := by simp [u]
    rw [h2, LinearIsometryEquiv.inner_map_map, lp.inner_single_right]
    simp
  have hs := lp.hasSum_inner (𝕜 := ℂ) (u r) (u r')
  have hv : inner ℂ (u r) (u r') = if r = r' then (1:ℂ) else 0 := by
    simp only [u, LinearIsometryEquiv.inner_map_map]
    rw [lp.inner_single_left]
    by_cases h : r = r'
    · subst h; simp
    · simp [lp.single_apply, h]
  rw [hv] at hs
  convert hs using 1
  funext c
  rw [hM, hM]
  simp [mul_comm]

section Rot
variable {B : Type*} [DecidableEq B]

/-- A real rotation on the two-dimensional block spanned by `p, q`, identity elsewhere. -/
noncomputable def rot (p q : B) (x i : B) : ℝ :=
  if x = p then (if i = p then 3/5 else if i = q then 4/5 else 0)
  else if x = q then (if i = p then -4/5 else if i = q then 3/5 else 0)
  else (if i = x then 1 else 0)

lemma two_point {p q : B} (hpq : p ≠ q) (f : B → ℂ) (α β : ℂ)
    (hf : ∀ c, f c = (if c = p then α else 0) + (if c = q then β else 0)) :
    HasSum f (α + β) := by
  have := (hasSum_ite_eq p α).add (hasSum_ite_eq q β)
  convert this using 1
  funext c; rw [hf]

lemma rot_rows {p q : B} (hpq : p ≠ q) (a b : B) :
    HasSum (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q b c : ℝ) : ℂ))
      (if a = b then 1 else 0) := by
  have hqp : q ≠ p := Ne.symm hpq
  by_cases ha : a = p ∨ a = q
  · by_cases hb : b = p ∨ b = q
    · have h := two_point hpq (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q b c : ℝ) : ℂ))
        (((rot p q a p : ℝ) : ℂ) * star ((rot p q b p : ℝ) : ℂ))
        (((rot p q a q : ℝ) : ℂ) * star ((rot p q b q : ℝ) : ℂ)) (fun c => by
          by_cases hc : c = p
          · subst hc; simp [hpq]
          · by_cases hc' : c = q
            · subst hc'; simp [hc]
            · rcases ha with rfl | rfl <;> simp [rot, hc, hc', hpq, hqp])
      convert h using 1
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [rot, hpq, hqp] <;> norm_num
    · push Not at hb
      have : (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q b c : ℝ) : ℂ)) = fun _ => 0 := by
        funext c
        by_cases hc : c = b
        · subst hc; rcases ha with rfl | rfl <;> simp [rot, hb.1, hb.2]
        · simp [rot, hb.1, hb.2, hc]
      rw [this, if_neg (by rintro rfl; rcases ha with h | h; exact hb.1 h; exact hb.2 h)]
      exact hasSum_zero
  · push Not at ha
    by_cases hb : b = p ∨ b = q
    · have : (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q b c : ℝ) : ℂ)) = fun _ => 0 := by
        funext c
        by_cases hc : c = a
        · subst hc; rcases hb with rfl | rfl <;> simp [rot, ha.1, ha.2]
        · simp [rot, ha.1, ha.2, hc]
      rw [this, if_neg (by rintro rfl; rcases hb with h | h; exact ha.1 h; exact ha.2 h)]
      exact hasSum_zero
    · push Not at hb
      have : (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q b c : ℝ) : ℂ)) =
          fun c => if c = a then (if a = b then 1 else 0) else 0 := by
        funext c
        by_cases hc : c = a
        · subst hc; by_cases hab : c = b
          · subst hab; simp [rot, ha.1, ha.2]
          · simp [rot, ha.1, ha.2, hb.1, hb.2, hab, Ne.symm hab]
        · simp [rot, ha.1, ha.2, hb.1, hb.2, hc]
      rw [this]; exact hasSum_ite_eq a _

lemma rot_transpose (p q : B) (hpq : p ≠ q) (r c : B) : rot p q r c = rot q p c r := by
  have hqp : q ≠ p := Ne.symm hpq
  unfold rot
  by_cases hr : r = p <;> by_cases hr' : r = q <;> by_cases hc : c = p <;> by_cases hc' : c = q <;>
    subst_vars <;> simp_all [eq_comm]

lemma rot_sq_real {p q : B} (hpq : p ≠ q) (a : B) :
    HasSum (fun c => (rot p q a c) ^ 2) 1 := by
  have h := rot_rows hpq a a
  simp only [if_pos rfl] at h
  have : (fun c => ((rot p q a c : ℝ) : ℂ) * star ((rot p q a c : ℝ) : ℂ)) =
      fun c => (((rot p q a c) ^ 2 : ℝ) : ℂ) := by
    funext c; simp [sq]
  rw [this] at h
  exact_mod_cast (Complex.hasSum_ofReal.1 (by simpa using h))

lemma ennreal_sq_of_real (t : ℝ) : ((‖(t : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (t ^ 2) := by
  rw [← ENNReal.coe_pow, ENNReal.ofReal, ← Real.toNNReal_coe (r := ‖(t:ℂ)‖₊ ^ 2)]
  congr 2
  simp [sq_abs]

lemma rot_cols {p q : B} (hpq : p ≠ q) (c : B) :
    ∑' r, ((‖((rot p q r c : ℝ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = 1 := by
  have h := rot_sq_real (Ne.symm hpq) c
  simp_rw [ennreal_sq_of_real, rot_transpose p q hpq _ c]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable, h.tsum_eq,
    ENNReal.ofReal_one]

lemma rot_sq {p q : B} (hpq : p ≠ q) (a : B) :
    Summable fun c => ‖((rot p q a c : ℝ) : ℂ)‖ ^ 2 := by
  simpa [Complex.norm_real, sq_abs] using (rot_sq_real hpq a).summable
end Rot

section Kernels
variable {B : Type*} [DecidableEq B]

/-- Good real kernels: orthonormal complex rows, unit columns, square-summable rows. -/
structure Good (K : B → B → ℝ) : Prop where
  rows : ∀ a b, HasSum (fun j => ((K a j : ℝ) : ℂ) * star ((K b j : ℝ) : ℂ)) (if a = b then 1 else 0)
  cols : ∀ j, ∑' r, ((‖((K r j : ℝ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = 1
  sq : ∀ a, Summable fun j => ‖((K a j : ℝ) : ℂ)‖ ^ 2

lemma good_rot {p q : B} (hpq : p ≠ q) : Good (rot p q) :=
  ⟨rot_rows hpq, rot_cols hpq, rot_sq hpq⟩

lemma good_id : Good (fun x j : B => if j = x then (1:ℝ) else 0) := by
  refine ⟨fun a b => ?_, fun j => ?_, fun a => ?_⟩
  · have : (fun j => (((if j = a then (1:ℝ) else 0) : ℝ) : ℂ) * star (((if j = b then (1:ℝ) else 0) : ℝ) : ℂ))
        = fun j => if j = a then (if a = b then 1 else 0) else 0 := by
      funext j; by_cases h : j = a
      · subst h; by_cases h' : j = b <;> simp [h']
      · simp [h]
    rw [this]; exact hasSum_ite_eq a _
  · have : (fun r => ((‖(((if j = r then (1:ℝ) else 0) : ℝ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2)
        = fun r => if r = j then 1 else 0 := by
      funext r; by_cases h : r = j
      · subst h; simp
      · simp [Ne.symm h, h]
    rw [this, tsum_ite_eq]
  · have : (fun j => ‖(((if j = a then (1:ℝ) else 0) : ℝ) : ℂ)‖ ^ 2) = fun j => if j = a then 1 else 0 := by
      funext j; by_cases h : j = a <;> simp [h]
    rw [this]; exact (hasSum_ite_eq a (1:ℝ)).summable

variable {O : Type*} [DecidableEq O]

/-- Lift a good kernel on `B` to a kernel `O × Unit → B × Unit → ℂ` via a bijection `τ`. -/
def liftK (K : B → B → ℝ) (τ : O ≃ B) : O × Unit → B × Unit → ℂ :=
  fun a c => ((K (τ a.1) c.1 : ℝ) : ℂ)

lemma liftK_good {K : B → B → ℝ} (hK : Good K) (τ : O ≃ B) :
    (∀ a, Summable fun c => ‖liftK K τ a c‖ ^ 2) ∧
    (∀ a b, HasSum (fun c => liftK K τ a c * star (liftK K τ b c)) (if a = b then 1 else 0)) ∧
    (∀ c, ∑' r, ((‖liftK K τ r c‖₊ : ℝ≥0∞)) ^ 2 = 1) := by
  refine ⟨fun a => ?_, fun a b => ?_, fun c => ?_⟩
  · exact ((Equiv.prodPUnit B).summable_iff (f := fun j => ‖((K (τ a.1) j : ℝ) : ℂ)‖ ^ 2)).2 (hK.sq _)
  · have h := ((Equiv.prodPUnit B).hasSum_iff
      (f := fun j => ((K (τ a.1) j : ℝ) : ℂ) * star ((K (τ b.1) j : ℝ) : ℂ))).2 (hK.rows _ _)
    have hab : (τ a.1 = τ b.1) ↔ a = b := by
      rw [τ.apply_eq_iff_eq]; exact ⟨fun h => Prod.ext h (Subsingleton.elim _ _), fun h => h ▸ rfl⟩
    simp only [hab] at h
    exact h
  · have h := ((Equiv.prodPUnit O).trans τ).tsum_eq
      (fun i => ((‖((K i c.1 : ℝ) : ℂ)‖₊ : ℝ≥0∞)) ^ 2)
    rw [← hK.cols c.1, ← h]
    rfl

lemma row_p_nonneg (p q j : B) : 0 ≤ rot p q p j := by
  unfold rot; simp only [if_pos rfl]; split_ifs <;> norm_num

end Kernels

section Witness
variable {O B : Type*} [DecidableEq O] [DecidableEq B] [AddCommGroup B]

lemma local_witness (e : O ≃ B) (x x' : O) (a a' : B) (h : x ≠ x' → a ≠ a') :
    ∃ V : O × Unit → B × Unit → ℂ,
      (∀ u, Summable fun c => ‖V u c‖ ^ 2) ∧
      (∀ u v, HasSum (fun c => V u c * star (V v c)) (if u = v then 1 else 0)) ∧
      (∀ c, ∑' r, ((‖V r c‖₊ : ℝ≥0∞)) ^ 2 = 1) ∧
      ∑' c : B × Unit, V (x, ()) (a + c.1, c.2) * star (V (x', ()) (a' + c.1, c.2)) ≠ 0 := by
  by_cases hA : x = x' ∧ a ≠ a'
  · obtain ⟨rfl, haa⟩ := hA
    set p := e x
    set q := p + (a - a')
    have hqp : q ≠ p := by
      intro hq; apply haa
      have : a - a' = 0 := by simpa [q] using hq
      exact sub_eq_zero.1 this
    refine ⟨liftK (rot p q) e, (liftK_good (good_rot (Ne.symm hqp)) e).1,
      (liftK_good (good_rot (Ne.symm hqp)) e).2.1, (liftK_good (good_rot (Ne.symm hqp)) e).2.2, ?_⟩
    set F : B → ℝ := fun i => rot p q p (a + i) * rot p q p (a' + i)
    have hF : ∀ i, 0 ≤ F i := fun i => mul_nonneg (row_p_nonneg _ _ _) (row_p_nonneg _ _ _)
    have hsum : Summable F := by
      have h1 := ((Equiv.addLeft a).summable_iff (f := fun j => (rot p q p j) ^ 2)).2
        (rot_sq_real (Ne.symm hqp) p).summable
      have h2 := ((Equiv.addLeft a').summable_iff (f := fun j => (rot p q p j) ^ 2)).2
        (rot_sq_real (Ne.symm hqp) p).summable
      refine Summable.of_nonneg_of_le hF (fun i => ?_) (h1.add h2)
      simp only [F, Function.comp, Equiv.coe_addLeft]
      nlinarith [sq_nonneg (rot p q p (a + i) - rot p q p (a' + i))]
    have hpos : 0 < ∑' i, F i := by
      refine Summable.tsum_pos hsum hF (p - a') ?_
      have e1 : a' + (p - a') = p := by abel
      have e2 : a + (p - a') = q := by simp only [q]; abel
      simp only [F, e1, e2, rot, if_neg hqp]
      norm_num
    have : ∑' c : B × Unit, liftK (rot p q) e (x, ()) (a + c.1, c.2) *
        star (liftK (rot p q) e (x, ()) (a' + c.1, c.2)) = ((∑' i, F i : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum, ← (Equiv.prodPUnit B).tsum_eq]
      congr 1; funext c
      simp [liftK, F, p]
    rw [this]
    exact_mod_cast hpos.ne'
  · set τ : O ≃ B := e.trans (Equiv.swap (e x') (e x + (a' - a)))
    have hτ : τ x' - a' = τ x - a := by
      by_cases hx : x = x'
      · subst hx
        have : a = a' := by by_contra h'; exact hA ⟨rfl, h'⟩
        rw [this]
      · have haa := h hx
        have h1 : τ x = e x := by
          simp only [τ, Equiv.trans_apply]
          refine Equiv.swap_apply_of_ne_of_ne (fun h' => hx (e.injective h')) (fun h' => ?_)
          apply haa
          have : a' - a = 0 := by
            have := congrArg (fun z => z - e x) h'; simpa using this.symm
          exact (sub_eq_zero.1 this).symm
        have h2 : τ x' = e x + (a' - a) := by simp [τ]
        rw [h1, h2]; abel
    refine ⟨liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ, (liftK_good good_id τ).1,
      (liftK_good good_id τ).2.1, (liftK_good good_id τ).2.2, ?_⟩
    have : ∑' c : B × Unit, liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ (x, ()) (a + c.1, c.2) *
        star (liftK (fun x j : B => if j = x then (1:ℝ) else 0) τ (x', ()) (a' + c.1, c.2))
        = ∑' i : B, if i = τ x - a then (1:ℂ) else 0 := by
      rw [← (Equiv.prodPUnit B).tsum_eq]
      congr 1; funext c
      simp only [liftK, Equiv.prodPUnit_apply]
      have k1 : (a + c.1 = τ x) ↔ c.1 = τ x - a := by
        constructor <;> intro h' <;> [rw [← h']; rw [h']] <;> abel
      have k2 : (a' + c.1 = τ x') ↔ c.1 = τ x - a := by
        rw [← hτ]; constructor <;> intro h' <;> [rw [← h']; rw [h']] <;> abel
      by_cases hc : c.1 = τ x - a
      · rw [if_pos (k1.2 hc), if_pos (k2.2 hc), if_pos hc]; simp
      · rw [if_neg (mt k1.1 hc), if_neg (mt k2.1 hc), if_neg hc]; simp
    rw [this, tsum_ite_eq]; exact one_ne_zero

end Witness

section Main
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*}
  [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)] [∀ k, Countable (O k)]
  [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

/-- **P1 (countable, no ancillas).** If the induced map is unitary on `ℓ²` for every family of
local unitaries (no ancillas), then `w` is exclusive. -/
theorem exclusive_of_unitary_l2 (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k))
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
  have hp := hasSum_pi_prod g hg
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

/-- **Countable no-ancilla converse (L.4(b)).** For countable abelian-group alphabets with
`O k ≃ I k`, the induced map is unitary for every family of local unitaries (no ancillas)
iff `w` is a process function. -/
theorem unitary_l2_noAncilla_iff_pf (e : ∀ k, O k ≃ I k) (w : (∀ k, O k) → (∀ k, I k)) :
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
    exact FiniteBox.existsUnique_of_exclusive w (exclusive_of_unitary_l2 e w h) f
  · intro hw V hsq hrow hcol
    obtain ⟨Φ, -, hΦ⟩ := induced_unitary_l2 w hw V hsq hrow hcol
    exact ⟨Φ, hΦ⟩

end Main

end PFUL.Countable

#print axioms PFUL.Countable.exclusive_of_unitary_l2
#print axioms PFUL.Countable.unitary_l2_noAncilla_iff_pf
