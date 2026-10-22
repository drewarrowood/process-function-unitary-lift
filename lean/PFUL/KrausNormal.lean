import PFUL.TraceNormDense
import PFUL.ChoiConverse

/-!
# Kraus ⟺ normal CPTP on countable `ℓ²`, and validity for normal CPTP local channels

* `krausIso V hiso : ℓ²(A) → ℓ²(O × Y)` is the Stinespring isometry of a Kraus kernel
  `V : O × Y → A → ℂ` (`⟨o|K_y|a⟩ = V (o, y) a`), and `krausChannel V hiso ρ = Tr_Y (U ρ U†)`
  (the form used in `valid_kraus_l2`). **Bridge:** `krausChannel_eq_stinespring` identifies it with
  the abstract Stinespring channel of the isometry `ℓ²(A) → ℓ²(Y; ℓ²(O))`, so it is normal CPTP
  (`isNormalCPTP_krausChannel`), and its Choi kernel is `choiKernel V` (`inner_krausChannel`).
* `choiOf Φ` is the Choi kernel of a map `Φ`; for CPTP `Φ` it is positive and trace-preserving.
* **`exists_kraus_of_normalCPTP`**: every normal CPTP map `𝒮₁(ℓ²(A)) → 𝒮₁(ℓ²(O))`, `A, O`
  countable, is `krausChannel V hiso` for a Kraus kernel over a countable Kraus index.
* **`valid_normalCPTP_l2`**: validity of the permutation lift for arbitrary normal CPTP local
  channels on countable alphabets.
-/

open ContinuousLinearMap Filter Topology PFUL.TraceClass
open scoped InnerProductSpace ComplexOrder ENNReal NNReal

set_option linter.unusedSectionVars false

universe u v

namespace PFUL.Countable

section Kraus
variable {O A Y : Type u} [DecidableEq O] [DecidableEq A] [DecidableEq Y]

theorem memℓp_col {V : O × Y → A → ℂ}
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) (a : A) :
    Memℓp (fun r => V r a) 2 := by
  refine memℓp_gen ?_
  have h := hiso a a
  simp_rw [star_mul_self_eq] at h
  simpa using (Complex.summable_ofReal.1 h.summable)

/-- The Stinespring isometry `ℓ²(A) → ℓ²(O × Y)` of a Kraus kernel. -/
noncomputable def krausIso (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) :
    lp (fun _ : A => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : O × Y => ℂ) 2 :=
  (show Orthonormal ℂ (fun a => (⟨fun r => V r a, memℓp_col hiso a⟩ : lp (fun _ : O × Y => ℂ) 2))
    from by
      rw [orthonormal_iff_ite]; intro a a'
      rw [inner_lp_eq_tsum]; exact (hiso a a').tsum_eq).orthogonalFamily.linearIsometry

theorem krausIso_single (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (a : A) (r : O × Y) : krausIso V hiso (lp.single 2 a (1 : ℂ)) r = V r a := by
  rw [krausIso, OrthogonalFamily.linearIsometry_apply_single]; simp

/-- The channel `ρ ↦ Tr_Y (U ρ U†)` of a Kraus kernel (as in `valid_kraus_l2`). -/
noncomputable def krausChannel (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (ρ : lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) :
    lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2 :=
  let U := (krausIso V hiso).toContinuousLinearMap
  ptraceR (U ∘L ρ ∘L adjoint U)

/-- The abstract Stinespring isometry `ℓ²(A) → ℓ²(Y; ℓ²(O))`. -/
noncomputable def krausStine (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) :
    lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : Y => lp (fun _ : O => ℂ) 2) 2 :=
  l2ProdCLM O Y ∘L (krausIso V hiso).toContinuousLinearMap

theorem krausStine_isometry (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) :
    adjoint (krausStine V hiso) ∘L krausStine V hiso = ContinuousLinearMap.id ℂ _ := by
  have hL : adjoint (l2ProdCLM O Y) ∘L l2ProdCLM O Y = ContinuousLinearMap.id ℂ _ :=
    adjoint_comp_self_linearIsometryEquiv _
  rw [krausStine, adjoint_comp, comp_assoc, ← comp_assoc (adjoint (l2ProdCLM O Y)), hL, id_comp,
    adjoint_comp_self_of_isometry]

/-- **Bridge:** the kernel-form channel is the abstract Stinespring channel. -/
theorem krausChannel_eq_stinespring (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) :
    krausChannel V hiso = stinespring (krausStine V hiso) := by
  funext ρ
  simp only [krausChannel, stinespring, krausStine, ptraceR, adjoint_comp, comp_assoc]

theorem isNormalCPTP_krausChannel (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) :
    IsNormalCPTP (krausChannel V hiso) := by
  rw [krausChannel_eq_stinespring]
  exact isNormalCPTP_stinespring _ (krausStine_isometry V hiso)

theorem inner_slot_krausStine (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (o : O) (y : Y) (a : A) :
    ⟪slot y (lp.single 2 o (1 : ℂ)), krausStine V hiso (lp.single 2 a 1)⟫_ℂ = V (o, y) a := by
  rw [← l2ProdEquiv_single, krausStine, comp_apply]
  change ⟪l2ProdEquiv O Y _, l2ProdEquiv O Y _⟫_ℂ = _
  rw [LinearIsometryEquiv.inner_map_map, inner_single_left']
  exact krausIso_single V hiso a (o, y)

theorem conj_rankOne {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (W : E →L[ℂ] F) (x y : E) :
    W ∘L InnerProductSpace.rankOne ℂ x y ∘L adjoint W = InnerProductSpace.rankOne ℂ (W x) (W y) := by
  rw [InnerProductSpace.rankOne_comp, InnerProductSpace.comp_rankOne, adjoint_adjoint]

/-- **Choi kernel of the kernel-form channel.** -/
theorem inner_krausChannel (V : O × Y → A → ℂ)
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (o o' : O) (a a' : A) :
    ⟪lp.single 2 o (1 : ℂ), krausChannel V hiso
      (InnerProductSpace.rankOne ℂ (lp.single 2 a 1) (lp.single 2 a' 1)) (lp.single 2 o' 1)⟫_ℂ =
      choiKernel V (o, a) (o', a') := by
  rw [krausChannel_eq_stinespring, stinespring]
  rw [conj_rankOne]
  have h := hasSum_inner_ptrace (rankOne_mem (krausStine V hiso (lp.single 2 a (1 : ℂ)))
    (krausStine V hiso (lp.single 2 a' 1))) (lp.single 2 o (1 : ℂ)) (lp.single 2 o' 1)
  refine h.unique ?_
  have hk := hasSum_choiKernel (O := O) (Y := Y) hiso (o, a) (o', a')
  convert hk using 1
  funext y
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_slot_krausStine,
    ← inner_conj_symm, inner_slot_krausStine]
  simp [mul_comm]

end Kraus

section ChoiOf
variable {O A : Type u} [DecidableEq O] [DecidableEq A]

/-- Choi kernel of a map: `J (o, a) (o', a') = ⟨o| Φ(|a⟩⟨a'|) |o'⟩`. -/
noncomputable def choiOf (Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
    (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)) (p q : O × A) : ℂ :=
  ⟪lp.single 2 p.1 (1 : ℂ),
    Φ (InnerProductSpace.rankOne ℂ (lp.single 2 p.2 1) (lp.single 2 q.2 1)) (lp.single 2 q.1 1)⟫_ℂ

theorem choiOf_tp {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
    (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} (hΦ : IsCPTP Φ) (a a' : A) :
    HasSum (fun o => choiOf Φ (o, a) (o, a')) (if a' = a then 1 else 0) := by
  have hm := hΦ.mem _ (rankOne_mem (lp.single 2 a (1 : ℂ)) (lp.single 2 a' 1))
  have h := hasSum_trace hm (default : HilbertBasis O ℂ (lp (fun _ : O => ℂ) 2))
  simp only [stdBasis_lp_apply] at h
  rw [hΦ.trace_eq _ (rankOne_mem _ _), trace_rankOne, inner_single_left', lp.single_apply,
    Pi.single_apply] at h
  exact h

theorem sum_slot_apply {Z : Type u} [DecidableEq Z] [Fintype Z] {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (w : Z → E) (z : Z) :
    (∑ p, slot p (w p) : lp (fun _ : Z => E) 2) z = w z := by
  rw [← adjoint_slot_apply, map_sum]
  simp only [adjoint_slot_apply, slot_apply]
  rw [Finset.sum_eq_single z (fun p _ hp => by simp [Pi.single_eq_of_ne' hp]) (by simp)]
  simp

theorem choiOf_psd {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
    (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} (hΦ : IsCPTP Φ) :
    KernelPSD (choiOf Φ) := by
  intro s c
  let Z := ↥s
  let Ω : lp (fun _ : Z => lp (fun _ : A => ℂ) 2) 2 := ∑ p : Z, slot p (lp.single 2 p.1.2 1)
  have hpos := hΦ.cp Z (InnerProductSpace.rankOne ℂ Ω Ω) (rankOne_mem Ω Ω)
    (InnerProductSpace.isPositive_rankOne_self Ω)
  let x : lp (fun _ : Z => lp (fun _ : O => ℂ) 2) 2 := ∑ p : Z, slot p (c p • lp.single 2 p.1.1 1)
  have h := hpos.inner_nonneg_right x
  rw [inner_ampMap] at h
  have hblk : ∀ z z' : Z, adjoint (slot z) ∘L InnerProductSpace.rankOne ℂ Ω Ω ∘L slot z' =
      InnerProductSpace.rankOne ℂ (lp.single 2 z.1.2 (1 : ℂ)) (lp.single 2 z'.1.2 1) := by
    intro z z'
    rw [← comp_assoc, InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp, adjoint_slot_apply,
      adjoint_slot_apply, sum_slot_apply, sum_slot_apply]
  simp only [hblk] at h
  simp only [x, sum_slot_apply] at h
  simp only [inner_smul_left, map_smul, inner_smul_right] at h
  rw [← Finset.sum_coe_sort s]
  convert h using 2 with z _
  rw [← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun z' _ => ?_
  simp only [choiOf, Complex.star_def]; ring

end ChoiOf

/-- `HilbertBasis` extensionality for bounded operators via matrix entries. -/
theorem clm_ext_entries {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) {X X' : E →L[ℂ] F} (h : ∀ i j, ⟪c j, X (b i)⟫_ℂ = ⟪c j, X' (b i)⟫_ℂ) :
    X = X' := by
  have hv : ∀ i, X (b i) = X' (b i) := fun i =>
    c.repr.injective (lp.ext (funext fun j => by simp [HilbertBasis.repr_apply_apply, h i j]))
  rw [← sub_eq_zero]
  have hker : Submodule.span ℂ (Set.range b) ≤ LinearMap.ker ((X - X' : E →L[ℂ] F) : E →ₗ[ℂ] F) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; simp [hv i])
  have hcl := Submodule.topologicalClosure_minimal _ hker ((X - X').isClosed_ker)
  rw [b.dense_span] at hcl
  ext x; exact hcl (Submodule.mem_top (x := x))

/-- **Kraus representation of normal CPTP maps on countable `ℓ²`** (the converse of
`isNormalCPTP_krausChannel`). -/
theorem exists_kraus_of_normalCPTP {O A : Type u} [Countable O] [Countable A] [DecidableEq O]
    [DecidableEq A] {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
      (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} (hΦ : IsNormalCPTP Φ) :
    ∃ (Y : Type u) (_ : Countable Y) (_ : DecidableEq Y) (V : O × Y → A → ℂ)
      (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)),
      ∀ ρ ∈ traceClass (lp (fun _ : A => ℂ) 2), Φ ρ = krausChannel V hiso ρ := by
  classical
  obtain ⟨Y, hY, V, hiso, hJ⟩ :=
    exists_kraus_of_choi (choiOf_psd hΦ.toIsCPTP) (choiOf_tp hΦ.toIsCPTP)
  refine ⟨Y, hY, inferInstance, V, hiso, ?_⟩
  set bA := (default : HilbertBasis A ℂ (lp (fun _ : A => ℂ) 2))
  set bO := (default : HilbertBasis O ℂ (lp (fun _ : O => ℂ) 2))
  refine eq_of_rankOne_basis hΦ (isNormalCPTP_krausChannel V hiso) bA fun a a' => ?_
  refine clm_ext_entries bO bO fun o' o => ?_
  simp only [bA, bO, stdBasis_lp_apply]
  rw [inner_krausChannel, hJ]
  rfl

theorem _root_.PFUL.TraceClass.IsNormalCPTP.congr {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {Φ Ψ : (H →L[ℂ] H) → (K →L[ℂ] K)} (hΨ : IsNormalCPTP Ψ)
    (h : ∀ T ∈ traceClass H, Φ T = Ψ T) : IsNormalCPTP Φ where
  mem T hT := by rw [h T hT]; exact hΨ.mem T hT
  map_add S hS T hT := by rw [h _ (add_mem hS hT), h S hS, h T hT]; exact hΨ.map_add S hS T hT
  map_smul a T hT := by
    rw [h _ (Submodule.smul_mem _ a hT), h T hT]; exact hΨ.map_smul a T hT
  trace_eq T hT := by rw [h T hT]; exact hΨ.trace_eq T hT
  cp Z _ _ T hT hpos := by
    have e : ampMap Z Φ T = ampMap Z Ψ T := by
      simp only [ampMap]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
      rw [h _ (sandwich_mem (H := lp (fun _ : Z => H) 2) (H' := H) _ _ hT)]
    rw [e]; exact hΨ.cp Z T hT hpos
  bounded := by
    obtain ⟨c, hc⟩ := hΨ.bounded
    exact ⟨c, fun T hT => by rw [h T hT]; exact hc T hT⟩

/-- **Kraus ⟺ normal CPTP on countable `ℓ²`.** -/
theorem isNormalCPTP_iff_kraus {O A : Type u} [Countable O] [Countable A] [DecidableEq O]
    [DecidableEq A] {Φ : (lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : A => ℂ) 2) →
      (lp (fun _ : O => ℂ) 2 →L[ℂ] lp (fun _ : O => ℂ) 2)} :
    IsNormalCPTP Φ ↔ ∃ (Y : Type u) (_ : Countable Y) (_ : DecidableEq Y) (V : O × Y → A → ℂ)
      (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)),
      ∀ ρ ∈ traceClass (lp (fun _ : A => ℂ) 2), Φ ρ = krausChannel V hiso ρ := by
  refine ⟨exists_kraus_of_normalCPTP, ?_⟩
  rintro ⟨Y, _, _, V, hiso, h⟩
  exact (isNormalCPTP_krausChannel V hiso).congr h

section Validity
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {I O X : ι → Type u}

/-- **Validity for arbitrary normal CPTP local channels on countable alphabets.** Every family of
normal CPTP local channels `Φ k : 𝒮₁(ℓ²(I k × X k)) → 𝒮₁(ℓ²(O k))` has Kraus kernels `V k` over
countable Kraus indices with `Φ k = krausChannel (V k)`, and for these the conclusions of
`valid_kraus_l2` hold: the induced operator is an isometry, and for every density operator `ρ`
the output and sink states are density operators and the Born pairing converges to `1`. -/
theorem valid_normalCPTP_l2 [∀ k, AddCommGroup (I k)] [∀ k, Countable (I k)]
    [∀ k, Countable (O k)] [∀ k, Countable (X k)] [∀ k, DecidableEq (I k)]
    [∀ k, DecidableEq (X k)] [∀ k, DecidableEq (O k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (Φ : ∀ k, (lp (fun _ : I k × X k => ℂ) 2 →L[ℂ] lp (fun _ : I k × X k => ℂ) 2) →
      (lp (fun _ : O k => ℂ) 2 →L[ℂ] lp (fun _ : O k => ℂ) 2))
    (hΦ : ∀ k, IsNormalCPTP (Φ k)) :
    ∃ (Y : ι → Type u) (_ : ∀ k, Countable (Y k)) (_ : ∀ k, DecidableEq (Y k))
      (V : ∀ k, O k × Y k → I k × X k → ℂ)
      (hiso : ∀ k c c', HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)),
      (∀ k, ∀ ρ ∈ traceClass (lp (fun _ : I k × X k => ℂ) 2),
        Φ k ρ = krausChannel (V k) (hiso k) ρ) ∧
      ∃ S : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →ₗᵢ[ℂ]
          lp (fun _ : (∀ k, O k) × (∀ k, Y k) => ℂ) 2,
        let U := S.toContinuousLinearMap
        (∀ r c, S (lp.single 2 c (1 : ℂ)) r = ∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k)) ∧
        (∀ r c, rowVec U r c = star (∏ k, V k (r.1 k, r.2 k) (w r.1 k + c.1 k, c.2 k))) ∧
        ∀ ρ : lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2 →L[ℂ]
            lp (fun _ : (∀ k, I k) × (∀ k, X k) => ℂ) 2, IsDensity ρ →
          IsDensity (U ∘L ρ ∘L adjoint U) ∧ IsDensity (ptraceR (U ∘L ρ ∘L adjoint U)) ∧
          HasSum (bornTerm U ρ) 1 ∧ (∀ r, 0 ≤ bornTerm U ρ r) ∧
            ∑' r, bornTerm U ρ r = trace (ptraceR (U ∘L ρ ∘L adjoint U)) := by
  choose Y hY hD V hiso hΦV using fun k => exists_kraus_of_normalCPTP (hΦ k)
  exact ⟨Y, hY, hD, V, hiso, hΦV, valid_kraus_l2 w hw V hiso⟩

end Validity

end PFUL.Countable
