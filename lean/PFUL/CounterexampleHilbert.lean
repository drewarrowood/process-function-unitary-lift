/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 12: the Switchboard with abstract Hilbert-space ancillas and normal CPTP channels

* `kerOf b A` : the matrix `⟪b r, A (b c)⟫` of an operator in a Hilbert basis.
  `isIsoKernel_kerOf`, `isCoIsoKernel_kerOf` : the matrix of a unitary in *any* Hilbert basis
  has orthonormal columns and rows (sums over arbitrary index sets).
* `IsPureHilbert`, `IsUnitaryKer.isPureHilbert`, `isPureHilbert_Vsb` : for **arbitrary** complex Hilbert spaces `H_k ≅ ℂ² ⊗ K_k` (any
  dimension, separable or not; given with a Hilbert basis indexed by `Bool × κ_k`, i.e. the
  product of the qubit basis and any Hilbert basis of `K_k`), arbitrary unitaries `A_k` of
  `H_k`, and any Hilbert space `G` with a Hilbert basis indexed by `P × ∏ κ_k` (a model of
  `ℂ^P ⊗ ⨂ K_k`), there is a unitary `U` of `G` whose matrix is the link product
  `compose Vsb (kerOf ∘ A)`. No separability or boundedness bookkeeping is needed: the result
  is transported from `isUnitaryKer_Vsb` along the Hilbert bases.
* `compose2`, `isIsoKernel_compose2_Vsb` : the link product with local operations whose input
  and output ancillas differ (`Bool × X_k → Bool × Y_k`), and the isometry of the closed loop
  for isometric local kernels on ancillas of any cardinality.
* `valid_normalCPTP_Vsb` : validity of the Switchboard against arbitrary **normal CPTP** local
  channels `𝒮₁(ℓ²(Bool × X_k)) → 𝒮₁(ℓ²(Bool × X'_k))` with countable (possibly infinite)
  ancilla alphabets: the closed loop is the normal CPTP channel of an isometric Kraus kernel,
  namely the link product of `Vsb` with the local Kraus kernels.
-/
import PFUL.CounterexampleAuto
import PFUL.KrausNormal

open Complex Finset
open scoped InnerProductSpace ComplexConjugate

namespace PFUL.Counterexample

/-! ## Abstract Hilbert spaces -/

section Hilbert
variable {X : Type} [DecidableEq X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The matrix of an operator in a Hilbert basis. -/
noncomputable def kerOf (b : HilbertBasis X ℂ H) (A : H → H) : Matrix X X ℂ := fun r c => ⟪b r, A (b c)⟫_ℂ

omit [CompleteSpace H] in
theorem isIsoKernel_kerOf (b : HilbertBasis X ℂ H) (A : H ≃ₗᵢ[ℂ] H) : IsIsoKernel (kerOf b A) := by
  intro c c'
  have h := b.hasSum_inner_mul_inner (A (b c)) (A (b c'))
  rw [LinearIsometryEquiv.inner_map_map, orthonormal_iff_ite.1 b.orthonormal c c'] at h
  refine h.congr_fun fun r => ?_
  simp only [kerOf]
  rw [← inner_conj_symm (b r) (A (b c))]
  simp only [starRingEnd_apply, star_star]

omit [CompleteSpace H] in
theorem isCoIsoKernel_kerOf (b : HilbertBasis X ℂ H) (A : H ≃ₗᵢ[ℂ] H) :
    IsCoIsoKernel (kerOf b A) := by
  intro r r'
  have h := b.hasSum_inner_mul_inner (A.symm (b r)) (A.symm (b r'))
  rw [LinearIsometryEquiv.inner_map_map, orthonormal_iff_ite.1 b.orthonormal r r'] at h
  refine h.congr_fun fun c => ?_
  simp only [kerOf]
  have e1 : ⟪b r, A (b c)⟫_ℂ = ⟪A.symm (b r), b c⟫_ℂ := by
    conv_lhs => rw [← A.apply_symm_apply (b r)]
    exact A.inner_map_map _ _
  have e2 : star ⟪b r', A (b c)⟫_ℂ = ⟪b c, A.symm (b r')⟫_ℂ := by
    rw [show star ⟪b r', A (b c)⟫_ℂ = conj ⟪b r', A (b c)⟫_ℂ from rfl, inner_conj_symm]
    conv_lhs => rw [← A.apply_symm_apply (b r')]
    exact A.inner_map_map _ _
  rw [e1, e2]

end Hilbert

/-- **Purity with ancillas in arbitrary Hilbert spaces.** For every family of complex Hilbert
spaces `H k` with Hilbert bases indexed by `Bool × κ k` (models of `ℂ² ⊗ K_k` for an arbitrary
Hilbert space `K_k` with Hilbert basis `κ k`), every family of unitaries `A k` of `H k`, and
every Hilbert space `G` with a Hilbert basis indexed by `P × ∏ κ_k`, there is a unitary `U`
of `G` whose matrix in that basis is the link product of `V` with the matrices of the `A k`. -/
def IsPureHilbert {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) : Prop :=
  ∀ (κ : Fin 3 → Type) [∀ k, DecidableEq (κ k)]
    (H : Fin 3 → Type) [∀ k, NormedAddCommGroup (H k)] [∀ k, InnerProductSpace ℂ (H k)]
    [∀ k, CompleteSpace (H k)] (b : ∀ k, HilbertBasis (Bool × κ k) ℂ (H k))
    (A : ∀ k, H k ≃ₗᵢ[ℂ] H k)
    (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (bG : HilbertBasis (P × (∀ k, κ k)) ℂ G),
    ∃ U : G ≃ₗᵢ[ℂ] G, ∀ r c, ⟪bG r, U (bG c)⟫_ℂ = compose V (fun k => kerOf (b k) (A k)) r c

/-- Kernel unitarity (`ℓ²(κ)`, any cardinality) transports to arbitrary Hilbert spaces, for
every `V`. -/
theorem IsUnitaryKer.isPureHilbert {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsUnitaryKer V) : IsPureHilbert V := by
  intro κ _ H _ _ _ b A G _ _ _ bG
  obtain ⟨U0, hU0⟩ := h κ (fun k => kerOf (b k) (A k))
    (fun k => isIsoKernel_kerOf (b k) (A k)) (fun k => isCoIsoKernel_kerOf (b k) (A k))
  refine ⟨bG.repr.trans (U0.trans bG.repr.symm), fun r c => ?_⟩
  rw [← hU0 r c, ← HilbertBasis.repr_apply_apply]
  simp [HilbertBasis.repr_self]

/-- **The Switchboard is pure against ancillas in arbitrary Hilbert spaces** (any dimension,
separable or not). -/
theorem isPureHilbert_Vsb : IsPureHilbert Vsb := isUnitaryKer_Vsb.isPureHilbert

/-- Conversely, purity with arbitrary Hilbert ancillas gives kernel unitarity (take
`H k = ℓ²(Bool × κ k)` with the standard basis; a unitary kernel is a bounded unitary by
`unitary_of_unitaryKernel`). So `IsPureHilbert V ↔ IsUnitaryKer V` for every `V`. -/
theorem IsPureHilbert.isUnitaryKer {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P}
    (h : IsPureHilbert V) : IsUnitaryKer V := by
  intro κ _ a hc hr
  choose A hA using fun k => unitary_of_unitaryKernel (a k) (hc k) (hr k)
  have hk : (fun k => kerOf (default : HilbertBasis (Bool × κ k) ℂ (L2 (Bool × κ k))) (A k)) = a := by
    funext k r c
    simp only [kerOf, PFUL.Countable.stdBasis_lp_apply, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    exact hA k r c
  obtain ⟨U, hU⟩ := h κ (fun k => L2 (Bool × κ k)) (fun _ => default) A
    (L2 (P × (∀ k, κ k))) default
  refine ⟨U, fun r c => ?_⟩
  have := hU r c
  rw [hk] at this
  rw [← this]
  simp only [PFUL.Countable.stdBasis_lp_apply, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

theorem isPureHilbert_iff_isUnitaryKer {P : Type} [Fintype P] [DecidableEq P] (V : Proc P P) :
    IsPureHilbert V ↔ IsUnitaryKer V :=
  ⟨IsPureHilbert.isUnitaryKer, IsUnitaryKer.isPureHilbert⟩

/-! ## Different input and output ancillas; normal CPTP channels -/

/-- The link product with local operations `Bool × X_k → Bool × Y_k`. -/
def compose2 {P F : Type} [Fintype P] [Fintype F] (V : Proc P F) {X Y : Fin 3 → Type}
    (A : ∀ k, Matrix (Bool × Y k) (Bool × X k) ℂ) :
    Matrix (F × (∀ k, Y k)) (P × (∀ k, X k)) ℂ :=
  fun φβ πα => ∑ o : Fin 8, ∑ e : Fin 8,
    V (e, φβ.1) (o, πα.1) * ∏ k, A k (bit k o, φβ.2 k) (bit k e, πα.2 k)

theorem compose2_Vsb_apply {X Y : Fin 3 → Type} (A : ∀ k, Matrix (Bool × Y k) (Bool × X k) ℂ)
    (o' u s t : Fin 8) (β : ∀ k, Y k) (α : ∀ k, X k) :
    compose2 Vsb A ((o', u), β) ((s, t), α) =
      board o' (u ^^^ t) s * ∏ k, A k (bit k o', β k) (bit k (u ^^^ t), α k) := by
  simp only [compose2, Vsb]
  simp_rw [xor_eq_iff' u, ite_and, ite_mul, zero_mul]
  rw [Finset.sum_eq_single o']
  · rw [Finset.sum_eq_single (u ^^^ t)]
    · simp
    · intro e _ he; simp [he]
    · simp
  · intro o _ ho; simp [Ne.symm ho]
  · simp

set_option maxHeartbeats 2000000 in
/-- The Switchboard's closed loop with isometric local kernels `Bool × X_k → Bool × Y_k`
(ancillas of any cardinality, input and output ancillas different) has orthonormal columns. -/
theorem isIsoKernel_compose2_Vsb {X Y : Fin 3 → Type} [∀ k, DecidableEq (X k)]
    (a : ∀ k, Matrix (Bool × Y k) (Bool × X k) ℂ) (ha : ∀ k, IsIsoKernel (a k)) :
    IsIsoKernel (compose2 Vsb a) := by
  rintro ⟨⟨s, t⟩, α⟩ ⟨⟨s', t'⟩, α'⟩
  set B : Fin 3 → Bool → Bool → Bool → ℂ := fun k x y z =>
    ∑' b : Y k, star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k) with hBdef
  have hsn : ∀ k x y z, Summable fun b : Y k =>
      ‖star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k)‖ := by
    intro k x y z
    exact summable_star_mul ((summable_sq_of_isIsoKernel (ha k) (y, α k)).comp_injective
      (Prod.mk_right_injective x)) ((summable_sq_of_isIsoKernel (ha k) (z, α' k)).comp_injective
      (Prod.mk_right_injective x))
  have hfib : ∀ k x y z, HasSum (fun b : Y k => star (a k (x, b) (y, α k)) * a k (x, b) (z, α' k))
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
  have hrow : ∀ o' u : Fin 8, HasSum (fun β : (∀ k, Y k) =>
      star (compose2 Vsb a ((o', u), β) ((s, t), α)) * compose2 Vsb a ((o', u), β) ((s', t'), α'))
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
    rw [compose2_Vsb_apply, compose2_Vsb_apply, star_mul, star_prod, Finset.prod_mul_distrib]
    ring
  have htot := hasSum_prod_fintype (fun q : (Fin 8 × Fin 8) × (∀ k, Y k) =>
      star (compose2 Vsb a q ((s, t), α)) * compose2 Vsb a q ((s', t'), α'))
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

/-- Regrouping `(F × ∏ X'_k) × ∏ Y_k ≃ F × ∏ (X'_k × Y_k)`. -/
def regroup (F : Type) (X' Y : Fin 3 → Type) :
    ((F × (∀ k, X' k)) × (∀ k, Y k)) ≃ (F × (∀ k, X' k × Y k)) where
  toFun r := (r.1.1, fun k => (r.1.2 k, r.2 k))
  invFun s := ((s.1, fun k => (s.2 k).1), fun k => (s.2 k).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A local Kraus kernel `(Bool × X') × Y → Bool × X`, viewed as a kernel
`Bool × (X' × Y) ← Bool × X` for `compose2`. -/
def krausMat {X X' Y : Type} (V : (Bool × X') × Y → Bool × X → ℂ) :
    Matrix (Bool × (X' × Y)) (Bool × X) ℂ := fun r c => V ((r.1, r.2.1), r.2.2) c

/-- The closed loop of `Vsb` with local Kraus kernels, as a Kraus kernel
`((Fin 8 × Fin 8) × ∏ X'_k) × ∏ Y_k ← (Fin 8 × Fin 8) × ∏ X_k`. -/
noncomputable def krausLoop {X X' Y : Fin 3 → Type} (V : ∀ k, (Bool × X' k) × Y k → Bool × X k → ℂ) :
    ((Fin 8 × Fin 8) × (∀ k, X' k)) × (∀ k, Y k) → (Fin 8 × Fin 8) × (∀ k, X k) → ℂ :=
  fun r c => compose2 Vsb (fun k => krausMat (V k)) (regroup _ X' Y r) c

theorem isIsoKernel_krausLoop {X X' Y : Fin 3 → Type} [∀ k, DecidableEq (X k)]
    (V : ∀ k, (Bool × X' k) × Y k → Bool × X k → ℂ)
    (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)) :
    ∀ c c', HasSum (fun r => star (krausLoop V r c) * krausLoop V r c') (if c = c' then 1 else 0) := by
  have ha : ∀ k, IsIsoKernel (krausMat (V k)) := by
    intro k c c'
    have h := hiso k c c'
    rw [← (Equiv.prodAssoc Bool (X' k) (Y k)).symm.hasSum_iff] at h
    exact h
  intro c c'
  have h := isIsoKernel_compose2_Vsb _ ha c c'
  rw [← (regroup _ X' Y).hasSum_iff] at h
  exact h

open PFUL.Countable PFUL.TraceClass in
/-- **Validity of the Switchboard against normal CPTP local channels on countable,
possibly infinite, ancillas.** Every family of normal CPTP local channels
`Φ k : B(ℓ²(Bool × X_k)) → B(ℓ²(Bool × X'_k))` has Kraus kernels `V k`, and the closed loop
(the link product of `Vsb` with the Kraus kernels, regrouped) is an isometric Kraus kernel
from `(Fin 8 × Fin 8) × ∏ X_k` to `((Fin 8 × Fin 8) × ∏ X'_k) × ∏ Y_k`, whose channel is
normal CPTP. -/
theorem valid_normalCPTP_Vsb {X X' : Fin 3 → Type} [∀ k, Countable (X k)]
    [∀ k, Countable (X' k)] [∀ k, DecidableEq (X k)] [∀ k, DecidableEq (X' k)]
    (Φ : ∀ k, (lp (fun _ : Bool × X k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X k => ℂ) 2) →
      (lp (fun _ : Bool × X' k => ℂ) 2 →L[ℂ] lp (fun _ : Bool × X' k => ℂ) 2))
    (hΦ : ∀ k, IsNormalCPTP (Φ k)) :
    ∃ (Y : Fin 3 → Type) (_ : ∀ k, DecidableEq (Y k))
      (V : ∀ k, (Bool × X' k) × Y k → Bool × X k → ℂ)
      (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)),
      (∀ k, ∀ ρ ∈ traceClass (lp (fun _ : Bool × X k => ℂ) 2),
        Φ k ρ = krausChannel (V k) (hiso k) ρ) ∧
      IsNormalCPTP (krausChannel (krausLoop V) (isIsoKernel_krausLoop V hiso)) := by
  have hk := fun k => exists_kraus_of_normalCPTP (hΦ k)
  choose Y hYc hYd V hiso hV using hk
  exact ⟨Y, hYd, V, hiso, hV, isNormalCPTP_krausChannel _ _⟩

end PFUL.Counterexample

#print axioms PFUL.Counterexample.isIsoKernel_kerOf
#print axioms PFUL.Counterexample.isCoIsoKernel_kerOf
#print axioms PFUL.Counterexample.IsUnitaryKer.isPureHilbert
#print axioms PFUL.Counterexample.isPureHilbert_Vsb
#print axioms PFUL.Counterexample.isPureHilbert_iff_isUnitaryKer
#print axioms PFUL.Counterexample.isIsoKernel_krausLoop
#print axioms PFUL.Counterexample.isIsoKernel_compose2_Vsb
#print axioms PFUL.Counterexample.valid_normalCPTP_Vsb
