/-
Infinite-dimensional (countable) ancillas for the H.12 counterexample.

Local operations are bounded operators on `ℓ²(Bool × κ_k)` with `κ_k` an arbitrary countable
type; the loop-closing (link product) is taken on matrix entries `⟨e_r, A e_c⟩`, which is the
same finite sum over the system strings as the matrix `compose`, and the composed map is the
bounded operator on `ℓ²(P × ∏ κ_k)` with these entries.
-/
import PFUL.ChoiLink
import PFUL.KrausL2

set_option linter.unusedSectionVars false

open Finset Matrix
open scoped InnerProductSpace

namespace PFUL.Counterexample

/-! ## Summation lemmas -/

/-- Product of two absolutely convergent series. -/
theorem hasSum_mul_norm {A B : Type} {f : A → ℂ} {g : B → ℂ} {a b : ℂ}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun y => ‖g y‖) (ha : HasSum f a)
    (hb : HasSum g b) :
    (Summable fun z : A × B => ‖f z.1 * g z.2‖) ∧ HasSum (fun z : A × B => f z.1 * g z.2) (a * b) := by
  refine ⟨hf.mul_norm hg, ?_⟩
  have := tsum_mul_tsum_of_summable_norm hf hg
  rw [ha.tsum_eq, hb.tsum_eq] at this
  rw [this]; exact (summable_mul_of_summable_norm hf hg).hasSum

/-- Products of absolutely summable families over a finite product of index types. -/
theorem hasSum_pi_prod : ∀ (n : ℕ) {κ : Fin n → Type} (g : ∀ k, κ k → ℂ) (s : Fin n → ℂ),
    (∀ k, Summable fun b => ‖g k b‖) → (∀ k, HasSum (g k) (s k)) →
    (Summable fun β : (∀ k, κ k) => ‖∏ k, g k (β k)‖) ∧
      HasSum (fun β : (∀ k, κ k) => ∏ k, g k (β k)) (∏ k, s k) := by
  intro n
  induction n with
  | zero =>
    intro κ g s _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨(hasSum_fintype _).summable, by simp⟩
  | succ n ih =>
    intro κ g s hn hs
    obtain ⟨ihn, ihs⟩ := ih (fun k => g k.succ) (fun k => s k.succ) (fun k => hn k.succ)
      (fun k => hs k.succ)
    let e := Fin.consEquiv κ
    have hcomp : (fun β : (∀ k, κ k) => ∏ k, g k (β k)) ∘ e =
        fun x => g 0 x.1 * ∏ k : Fin n, g k.succ (x.2 k) := by
      funext x
      simp only [Function.comp_apply, e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
    obtain ⟨hn2, hs2⟩ := hasSum_mul_norm (A := κ 0) (B := ∀ k : Fin n, κ k.succ) (hn 0) ihn (hs 0) ihs
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      have : (fun β : (∀ k, κ k) => ‖∏ k, g k (β k)‖) ∘ e =
          fun x => ‖g 0 x.1 * ∏ k : Fin n, g k.succ (x.2 k)‖ := by
        funext x; exact congrArg norm (congrFun hcomp x)
      rw [this]; exact hn2
    · rw [← e.hasSum_iff, hcomp, Fin.prod_univ_succ]; exact hs2

/-- Assembling a series on `P × B` (with `P` finite) from its fibres. -/
theorem hasSum_prod_fintype {P B : Type} [Fintype P] [DecidableEq P] (f : P × B → ℂ) (g : P → ℂ)
    (h : ∀ p, HasSum (fun b => f (p, b)) (g p)) : HasSum f (∑ p, g p) := by
  have hsum : HasSum (fun x : P × B => ∑ p, Function.extend (fun b : B => (p, b))
      (fun b => f (p, b)) 0 x) (∑ p, g p) :=
    hasSum_sum fun p _ => (hasSum_extend_zero (Prod.mk_right_injective p)).2 (h p)
  convert hsum using 1
  funext ⟨p, b⟩
  rw [Finset.sum_eq_single p]
  · exact ((Prod.mk_right_injective p).extend_apply (fun b => f (p, b)) 0 b).symm
  · intro q _ hq
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨b', hb'⟩; exact hq (congrArg Prod.fst hb')
  · simp

theorem summable_star_mul {R : Type} {u v : R → ℂ} (hu : Summable fun r => ‖u r‖ ^ 2)
    (hv : Summable fun r => ‖v r‖ ^ 2) : Summable fun r => ‖star (u r) * v r‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_) (hu.add hv)
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖u r‖ - ‖v r‖), norm_nonneg (u r), norm_nonneg (v r)]


/-! ## Operators on ℓ² and their kernels -/

/-- `ℓ²(X)`. -/
noncomputable abbrev L2 (X : Type) := lp (fun _ : X => ℂ) 2

/-- Matrix entries `⟨e_r, A e_c⟩` of a bounded operator on `ℓ²(X)`. -/
noncomputable def entOp {X : Type} [DecidableEq X] (A : L2 X →L[ℂ] L2 X) : Matrix X X ℂ :=
  fun r c => A (lp.single 2 c (1 : ℂ)) r

/-- A kernel with orthonormal columns (the kernel of an isometry), sums over arbitrary index sets. -/
def IsIsoKernel {X Y : Type} [DecidableEq X] (a : Matrix Y X ℂ) : Prop :=
  ∀ c c', HasSum (fun r => star (a r c) * a r c') (if c = c' then 1 else 0)

theorem hasSum_inner_lp {R : Type} (f g : L2 R) :
    HasSum (fun r => star (f r) * g r) ⟪f, g⟫_ℂ := by
  have hs : Summable fun r => star (f r) * g r :=
    (lp.summable_inner f g).congr fun r => by simp [mul_comm]
  rw [PFUL.Countable.inner_lp_eq_tsum]; exact hs.hasSum

/-- The kernel of a unitary (indeed of any isometry) on `ℓ²` has orthonormal columns. -/
theorem isIsoKernel_entOp {X : Type} [DecidableEq X] (A : L2 X →L[ℂ] L2 X)
    (hA : A ∈ unitary (L2 X →L[ℂ] L2 X)) : IsIsoKernel (entOp A) := by
  intro c c'
  have h := hasSum_inner_lp (A (lp.single 2 c (1 : ℂ))) (A (lp.single 2 c' (1 : ℂ)))
  have hiso : ∀ x y : L2 X, ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
      Unitary.star_mul_self_of_mem hA, one_apply_eq_self]
  rw [hiso, lp.inner_single_left] at h
  convert h using 1
  · rfl
  rw [lp.single_apply]
  by_cases hc : c = c'
  · subst hc; simp
  · simp [hc]

/-- A kernel with orthonormal columns is the kernel of a linear isometry of `ℓ²`. -/
theorem exists_isometry_of_isIsoKernel {X Y : Type} [DecidableEq X] (M : Matrix Y X ℂ)
    (hG : IsIsoKernel M) :
    ∃ U : L2 X →ₗᵢ[ℂ] L2 Y, ∀ r c, U (lp.single 2 c (1 : ℂ)) r = M r c := by
  have hmem : ∀ c, Memℓp (fun r => M r c) 2 := by
    intro c
    refine memℓp_gen ?_
    have h := hG c c
    simp_rw [PFUL.Countable.star_mul_self_eq] at h
    have h' : Summable fun r => ‖M r c‖ ^ 2 := Complex.summable_ofReal.1 h.summable
    simpa using h'
  let m : X → L2 Y := fun c => ⟨fun r => M r c, hmem c⟩
  have hon : Orthonormal ℂ m := by
    rw [orthonormal_iff_ite]
    intro c c'
    rw [PFUL.Countable.inner_lp_eq_tsum]
    exact (hG c c').tsum_eq
  refine ⟨hon.orthogonalFamily.linearIsometry, fun r c => ?_⟩
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [m]

theorem summable_sq_of_isIsoKernel {X Y : Type} [DecidableEq X] {a : Matrix Y X ℂ} (ha : IsIsoKernel a) (c : X) :
    Summable fun r => ‖a r c‖ ^ 2 := by
  have h := ha c c
  simp_rw [PFUL.Countable.star_mul_self_eq] at h
  exact Complex.summable_ofReal.1 h.summable

/-! ## Purity with countable ancillas -/

/-- Kernel-level purity: for all ancilla types and all local isometric kernels on
`Bool × κ_k`, the composed kernel has orthonormal columns (the composed map is an isometry). -/
def IsPureKer {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, DecidableEq (κ k)] (a : ∀ k, Matrix (Bool × κ k) (Bool × κ k) ℂ),
    (∀ k, IsIsoKernel (a k)) → IsIsoKernel (compose V a)

/-- The bounded-operator link product: the loop closed with bounded local operators `A k` on
`ℓ²(Bool × κ_k)`; its kernel is `compose V (entOp ∘ A)`. -/
noncomputable def composeOp {P : Type} [Fintype P] (V : Proc P P) {κ : Fin 3 → Type}
    [∀ k, DecidableEq (κ k)] (A : ∀ k, L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k)) :
    Matrix (P × (∀ k, κ k)) (P × (∀ k, κ k)) ℂ :=
  compose V fun k => entOp (A k)

/-- **Purity against countable (possibly infinite-dimensional) ancillas**: for every family of
countable ancilla types and unitaries `A k` on `ℓ²(Bool × κ_k)`, the closed loop is a linear
isometry of `ℓ²(P × ∏ κ_k)` whose matrix is the link product `composeOp V A`. -/
def IsPureInf {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, Countable (κ k)] [∀ k, DecidableEq (κ k)]
    (A : ∀ k, L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k)),
    (∀ k, A k ∈ unitary (L2 (Bool × κ k) →L[ℂ] L2 (Bool × κ k))) →
      ∃ U : L2 (P × (∀ k, κ k)) →ₗᵢ[ℂ] L2 (P × (∀ k, κ k)),
        ∀ r c, U (lp.single 2 c (1 : ℂ)) r = composeOp V A r c

theorem IsPureKer.isPureInf {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsPureKer V) : IsPureInf V := by
  intro κ _ _ A hA
  exact exists_isometry_of_isIsoKernel _ (h κ _ fun k => isIsoKernel_entOp (A k) (hA k))

/-- Agreement with the matrix version: on finite ancillas, kernel purity gives `IsPure`
(the link product is literally the same finite sum, and a finite matrix with orthonormal
columns is unitary). -/
theorem IsPureKer.isPure {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsPureKer V) : IsPure V := by
  intro a _ _ A hA
  have hk : ∀ k, IsIsoKernel (A k) := by
    intro k c c'
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 (hA k)) c) c'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.star_apply] at this
    rw [← this]; exact hasSum_fintype _
  have hG := h a A hk
  rw [Matrix.mem_unitaryGroup_iff']
  ext c c'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  exact (hasSum_fintype _).unique (hG c c')

set_option maxHeartbeats 2000000 in
/-- **Goal (2)**: the Switchboard is pure against all ancillas (kernel form). The proof is the
finite one with the ancilla sums replaced by absolutely convergent series. -/
theorem isPureKer_Vsb : IsPureKer Vsb := by
  intro κ _ a ha
  rintro ⟨⟨s, t⟩, α⟩ ⟨⟨s', t'⟩, α'⟩
  set B : Fin 3 → Bool → Bool → Bool → ℂ := fun k x y z =>
    ∑' b : κ k, star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k) with hBdef
  have hsn : ∀ k x y z, Summable fun b : κ k =>
      ‖star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k)‖ := by
    intro k x y z
    exact summable_star_mul ((summable_sq_of_isIsoKernel (ha k) (y, α k)).comp_injective
      (Prod.mk_right_injective x)) ((summable_sq_of_isIsoKernel (ha k) (z, α' k)).comp_injective
      (Prod.mk_right_injective x))
  have hfib : ∀ k x y z, HasSum (fun b : κ k => star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k))
      (B k x y z) := fun k x y z => (hsn k x y z).of_norm.hasSum
  have hB : ∀ k y z, B k false y z + B k true y z =
      if y = z then (if α k = α' k then 1 else 0) else 0 := by
    intro k y z
    have h1 := (ha k (y, α k) (z, α' k)).prod_fiberwise fun x => hfib k x y z
    have h2 := (hasSum_fintype fun x : Bool => B k x y z).unique h1
    rw [Fintype.sum_bool] at h2
    rw [add_comm, h2]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  -- the fibre over a system output `(o', u)`
  have hrow : ∀ o' u : Fin 8, HasSum (fun β : (∀ k, κ k) =>
      star (compose Vsb a ((o', u), β) ((s, t), α)) * compose Vsb a ((o', u), β) ((s', t'), α'))
      (star (board o' (u ^^^ t) s) * board o' (u ^^^ t') s' *
        ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k (u ^^^ t'))) := by
    intro o' u
    obtain ⟨-, hp⟩ := hasSum_pi_prod 3
      (fun k b => star (a k (bit k o', b) (bit k (u ^^^ t), α k)) *
        a k (bit k o', b) (bit k (u ^^^ t'), α' k))
      (fun k => B k (bit k o') (bit k (u ^^^ t)) (bit k (u ^^^ t')))
      (fun k => hsn k _ _ _) (fun k => hfib k _ _ _)
    convert hp.mul_left (star (board o' (u ^^^ t) s) * board o' (u ^^^ t') s') using 1
    funext β
    rw [compose_Vsb_apply, compose_Vsb_apply, star_mul, star_prod, Finset.prod_mul_distrib]
    ring
  have htot := hasSum_prod_fintype (fun q : (Fin 8 × Fin 8) × (∀ k, κ k) =>
      star (compose Vsb a q ((s, t), α)) * compose Vsb a q ((s', t'), α'))
    (fun p : Fin 8 × Fin 8 => star (board p.1 (p.2 ^^^ t) s) * board p.1 (p.2 ^^^ t') s' *
        ∏ k, B k (bit k p.1) (bit k (p.2 ^^^ t)) (bit k (p.2 ^^^ t')))
    fun p => hrow p.1 p.2
  convert htot using 1
  rw [Fintype.sum_prod_type]
  simp only
  have hsh : ∀ o', ∑ u : Fin 8, star (board o' (u ^^^ t) s) * board o' (u ^^^ t') s' *
      ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k (u ^^^ t')) =
      ∑ e : Fin 8, star (board o' e s) * board o' (e ^^^ (t ^^^ t')) s' *
        ∏ k, B k (bit k o') (bit k e) (bit k (e ^^^ (t ^^^ t'))) := by
    intro o'
    have : ∀ u : Fin 8, star (board o' (u ^^^ t) s) * board o' (u ^^^ t') s' *
        ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k (u ^^^ t')) =
        star (board o' (u ^^^ t) s) * board o' ((u ^^^ t) ^^^ (t ^^^ t')) s' *
        ∏ k, B k (bit k o') (bit k (u ^^^ t)) (bit k ((u ^^^ t) ^^^ (t ^^^ t'))) := by
      intro u; rw [← xor_shift u t t']
    rw [Finset.sum_congr rfl fun u _ => this u]
    exact Fintype.sum_equiv (Function.Involutive.toPerm (fun u => u ^^^ t)
      (fun u => xor_xor_cancel' u t)) _ _ (fun u => rfl)
  simp_rw [hsh]
  rw [scalar_key B _ hB s s' (t ^^^ t')]
  simp only [xor_eq_zero_iff', Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, Prod.mk.injEq]
  have hα : (∀ k, α k = α' k) ↔ α = α' := funext_iff.symm
  simp only [hα]
  by_cases h1 : s = s' <;> by_cases h2 : t = t' <;> by_cases h3 : α = α' <;> simp [h1, h2, h3]

/-- The Switchboard is pure against countable, possibly infinite-dimensional, ancillas: its
closed loop with any local unitaries on `ℓ²(Bool × κ_k)` is an isometry of `ℓ²`. -/
theorem isPureInf_Vsb : IsPureInf Vsb := isPureKer_Vsb.isPureInf

/-- Purifiability with infinite-dimensional (countable) ancillas. -/
def PurifiableInf (p : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∃ (V : Proc (Fin 8 × Fin 8) (Fin 8 × Fin 8)) (ψ : Fin 8 × Fin 8 → ℂ),
    (∑ π, ‖ψ π‖ ^ 2) = 1 ∧ IsPureInf V ∧ IsPure V ∧ p = inducedP V ψ

/-- **Theorem H.12.1 with countable ancillas.** There is a valid three-party binary classical
process, purifiable by a process that stays pure against arbitrary countable ancillas, that is
not a mixture of process functions. -/
theorem purification_conjecture_false_inf :
    ∃ p : Fin 8 → Fin 8 → ℝ, Valid p ∧ PurifiableInf p ∧
      p ∉ convexHull ℝ {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
        (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} := by
  have hset : {x | ∃ w, PFUL.Countable.IsProcessFunction (I := fun _ : Fin 3 => Bool)
      (O := fun _ : Fin 3 => Bool) (wBits w) ∧ x = pfPoint w} = PFset := by
    ext x; simp only [PFset, Set.mem_ofPred_eq, isPF_iff]
  have h3 := pcl_not_mem_convexHull
  rw [← hset] at h3
  exact ⟨pcl, valid_pcl, ⟨Vsb, psiSrc, norm_psiSrc, isPureInf_Vsb, isPure_Vsb, inducedP_Vsb⟩, h3⟩

end PFUL.Counterexample
