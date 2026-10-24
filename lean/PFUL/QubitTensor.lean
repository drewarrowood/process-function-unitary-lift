/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Round 13: the local ancilla spaces `C² ⊗ K` are Hilbert spaces with a basis `Bool × κ`

`IsPureHilbert` quantifies over local Hilbert spaces `H_k` with a Hilbert basis indexed by
`Bool × κ_k`; in Round 12 the identification of these with `C² ⊗ K_k` was labelled
INTERPRETIVE. Here it is proved for Mathlib's inner-product tensor product
`EuclideanSpace ℂ Bool ⊗[ℂ] K` (Mathlib.Analysis.InnerProductSpace.TensorProduct):

* `qsplitEquiv` : `C² ⊗ K ≃ₗᵢ K ⊕₂ K` (so `C² ⊗ K` is complete when `K` is: no completion is
  needed since one factor is finite-dimensional);
* `qubitBasis B` : for a Hilbert basis `B` of `K` indexed by `κ`, the vectors `|b⟩ ⊗ B j`
  form a Hilbert basis of `C² ⊗ K` indexed by `Bool × κ`;
* `isPure_qubitTensor` : finite purity gives a unitary link for unitaries on `C² ⊗ K_k`.
-/
import PFUL.PureFiniteInf
import Mathlib.Analysis.InnerProductSpace.TensorProduct

open scoped TensorProduct InnerProductSpace
open TensorProduct

set_option linter.unusedSectionVars false

namespace PFUL.Counterexample

/-- The qubit `C²`. -/
abbrev Qb := EuclideanSpace ℂ Bool

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- `e ⊗ k ↦ (e₀ k, e₁ k)`. -/
noncomputable def qsplit : Qb ⊗[ℂ] K →ₗ[ℂ] PiLp 2 (fun _ : Bool => K) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (e : Qb) (k : K) => WithLp.toLp 2 (fun b => e b • k))
    (fun e e' k => by ext b; simp [add_smul])
    (fun c e k => by ext b; simp [mul_smul])
    (fun e k k' => by ext b; simp [smul_add])
    (fun c e k => by ext b; simp [smul_comm c]))

theorem qsplit_tmul (e : Qb) (k : K) : qsplit (e ⊗ₜ k) = WithLp.toLp 2 (fun b => e b • k) := rfl

theorem inner_qsplit (x y : Qb ⊗[ℂ] K) : ⟪qsplit x, qsplit y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [inner_add_left, hx, hx']
  | tmul e k =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [inner_add_right, hy, hy']
    | tmul e' k' =>
      rw [qsplit_tmul, qsplit_tmul, inner_tmul, PiLp.inner_apply, PiLp.inner_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [inner_smul_left, inner_smul_right, RCLike.inner_apply]
      ring

/-- **`C² ⊗ K ≃ K ⊕₂ K` isometrically.** -/
noncomputable def qsplitEquiv : (Qb ⊗[ℂ] K) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Bool => K) :=
  LinearIsometryEquiv.ofSurjective (qsplit.isometryOfInner inner_qsplit) fun g => by
    refine ⟨∑ b, EuclideanSpace.single b (1 : ℂ) ⊗ₜ g b, ?_⟩
    show qsplit _ = g
    rw [map_sum]
    ext b'
    simp [qsplit_tmul, PiLp.single_apply]
    cases b' <;> simp

/-- `C² ⊗ K` is complete when `K` is. -/
instance completeSpace_qubitTensor [CompleteSpace K] : CompleteSpace (Qb ⊗[ℂ] K) :=
  (completeSpace_congr (e := (qsplitEquiv (K := K)).toEquiv)
    (qsplitEquiv (K := K)).isometry.isUniformEmbedding).2 inferInstance

variable {κ : Type} [CompleteSpace K]

theorem orthonormal_qubit (B : HilbertBasis κ ℂ K) :
    Orthonormal ℂ fun p : Bool × κ => EuclideanSpace.single p.1 (1 : ℂ) ⊗ₜ[ℂ] B p.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨b, j⟩ ⟨b', j'⟩
  rw [inner_tmul, EuclideanSpace.inner_single_left, orthonormal_iff_ite.1 B.orthonormal j j']
  simp only [PiLp.single_apply, map_one, one_mul, Prod.mk.injEq]
  by_cases h1 : b' = b <;> by_cases h2 : j = j' <;> simp [h1, h2]

theorem dense_qubit (B : HilbertBasis κ ℂ K) :
    ⊤ ≤ (Submodule.span ℂ (Set.range fun p : Bool × κ =>
      EuclideanSpace.single p.1 (1 : ℂ) ⊗ₜ[ℂ] B p.2)).topologicalClosure := by
  classical
  set S := Submodule.span ℂ (Set.range fun p : Bool × κ =>
      EuclideanSpace.single p.1 (1 : ℂ) ⊗ₜ[ℂ] B p.2)
  have hk : ∀ (b : Bool) (k : K), EuclideanSpace.single b (1 : ℂ) ⊗ₜ[ℂ] k ∈ S.topologicalClosure := by
    intro b k
    have hkB : k ∈ closure (Submodule.span ℂ (Set.range B) : Set K) := by
      rw [← Submodule.topologicalClosure_coe, B.dense_span]; trivial
    let L : K →L[ℂ] Qb ⊗[ℂ] K := mkL ℂ Qb K (EuclideanSpace.single b 1)
    have := map_mem_closure L.continuous hkB (t := (S : Set (Qb ⊗[ℂ] K))) (by
      intro y hy
      have hmap : (Submodule.span ℂ (Set.range B)).map (L : K →ₗ[ℂ] Qb ⊗[ℂ] K) ≤ S := by
        rw [Submodule.map_span_le]
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨(b, j), rfl⟩
      exact hmap ⟨y, hy, rfl⟩)
    rw [← Submodule.topologicalClosure_coe] at this
    exact this
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul e k =>
    have he : e = ∑ b, e b • EuclideanSpace.single b (1 : ℂ) := by
      ext b'; simp [PiLp.single_apply]; cases b' <;> simp
    rw [he, TensorProduct.sum_tmul]
    exact Submodule.sum_mem _ fun b _ => by
      rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ _ (hk b k)

/-- **Hilbert basis of `C² ⊗ K` indexed by `Bool × κ`.** -/
noncomputable def qubitBasis (B : HilbertBasis κ ℂ K) : HilbertBasis (Bool × κ) ℂ (Qb ⊗[ℂ] K) :=
  HilbertBasis.mk (orthonormal_qubit B) (dense_qubit B)

theorem qubitBasis_apply (B : HilbertBasis κ ℂ K) (p : Bool × κ) :
    qubitBasis B p = EuclideanSpace.single p.1 (1 : ℂ) ⊗ₜ[ℂ] B p.2 := by
  simp [qubitBasis]

/-- **Finite purity, ancillas `C² ⊗ K_k`**: for every pure `V`, Hilbert spaces `K_k` of any
dimension with Hilbert bases `B_k`, unitaries `A_k` of `C² ⊗ K_k` (Mathlib's tensor product)
and every Hilbert space `G` with a Hilbert basis indexed by `P × ∏ κ_k`, the link product is
the matrix of a unitary of `G`. -/
theorem isPure_qubitTensor {P : Type} [Fintype P] [DecidableEq P] {V : Proc P P} (hV : IsPure V)
    (κ : Fin 3 → Type) [∀ k, DecidableEq (κ k)] (K : Fin 3 → Type) [∀ k, NormedAddCommGroup (K k)]
    [∀ k, InnerProductSpace ℂ (K k)] [∀ k, CompleteSpace (K k)] (B : ∀ k, HilbertBasis (κ k) ℂ (K k))
    (A : ∀ k, (Qb ⊗[ℂ] K k) ≃ₗᵢ[ℂ] (Qb ⊗[ℂ] K k))
    (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (bG : HilbertBasis (P × (∀ k, κ k)) ℂ G) :
    ∃ U : G ≃ₗᵢ[ℂ] G, ∀ r c, ⟪bG r, U (bG c)⟫_ℂ =
      compose V (fun k => kerOf (qubitBasis (B k)) (A k)) r c :=
  isPureHilbert_of_isPure hV κ (fun k => Qb ⊗[ℂ] K k) (fun k => qubitBasis (B k)) A G bG

end PFUL.Counterexample
