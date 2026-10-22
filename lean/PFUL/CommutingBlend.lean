import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The commuting Switchboard case (H.8.4), finite dimensions: linear-algebra core

For each joint output `o`, let `u o` be an orthonormal basis of the source space `E` (the rows
`U_o† |i⟩`, so `P_{o,i} = |u o i⟩⟨u o i|` and `p_φ(i|o) = |⟪u o i, φ⟫|²`). If all the rank-one
projectors `P_{o,i}` commute with those of a reference orthonormal basis `b` (e.g. `b = u o₀`
when all `P_{o,i}` commute pairwise), then

* `inner_eq_zero_or_norm_eq_one`: two commuting rank-one projectors onto unit vectors are equal or
  orthogonal;
* **`commuting_blend`**: there are deterministic conditionals `f j : outputs → inputs`, one per basis
  vector `b j`, with `p_φ(i|o) = ∑_j |⟪b j, φ⟫|² [f j o = i]` and `∑_j |⟪b j, φ⟫|² = ‖φ‖²`.

So `p_φ` is a convex mixture of the deterministic conditionals `f j`, which are the records of the
source states `b j`. That each `f j` is a process function (validity of the 0/1 record, Appendix A)
is not formalised here.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

namespace PFUL.Switchboard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two commuting rank-one projectors onto unit vectors: the vectors are parallel or orthogonal. -/
theorem inner_eq_zero_or_norm_eq_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : InnerProductSpace.rankOne ℂ u u ∘L InnerProductSpace.rankOne ℂ v v =
      InnerProductSpace.rankOne ℂ v v ∘L InnerProductSpace.rankOne ℂ u u) :
    ⟪u, v⟫_ℂ = 0 ∨ ‖⟪u, v⟫_ℂ‖ = 1 := by
  rw [InnerProductSpace.rankOne_comp_rankOne, InnerProductSpace.rankOne_comp_rankOne] at h
  have h1 := congrArg (fun T => ⟪u, T v⟫_ℂ) h
  simp only [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_right] at h1
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
  rw [hvv, huu, ← inner_conj_symm u v] at h1
  by_cases h0 : ⟪u, v⟫_ℂ = 0
  · exact Or.inl h0
  right
  have hc : (starRingEnd ℂ) ⟪v, u⟫_ℂ ≠ 0 := by rwa [inner_conj_symm]
  have h2 : ⟪v, u⟫_ℂ * (starRingEnd ℂ) ⟪v, u⟫_ℂ = 1 := by
    have : (starRingEnd ℂ) ⟪v, u⟫_ℂ * 1 =
        (starRingEnd ℂ) ⟪v, u⟫_ℂ * (⟪v, u⟫_ℂ * (starRingEnd ℂ) ⟪v, u⟫_ℂ) := by
      linear_combination h1
    exact (mul_left_cancel₀ hc this).symm
  rw [Complex.mul_conj'] at h2
  have h3 : ‖⟪v, u⟫_ℂ‖ ^ 2 = 1 := by exact_mod_cast h2
  rw [norm_inner_symm]
  nlinarith [norm_nonneg ⟪v, u⟫_ℂ, sq_nonneg (‖⟪v, u⟫_ℂ‖ - 1)]

theorem exists_indicator {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (h01 : ∀ a, w a = 0 ∨ w a = 1) (hs : ∑ a, w a = 1) :
    ∃ a₀, ∀ a, w a = if a = a₀ then 1 else 0 := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, w a₀ ≠ 0 := by
    by_contra hc; push Not at hc; simp [hc] at hs
  have h1 : w a₀ = 1 := (h01 a₀).resolve_left ha₀
  have hrest : ∑ a ∈ Finset.univ.erase a₀, w a = 0 := by
    have := Finset.add_sum_erase Finset.univ w (Finset.mem_univ a₀); linarith
  have hnn : ∀ a ∈ Finset.univ.erase a₀, 0 ≤ w a := fun a _ => by
    rcases h01 a with h | h <;> simp [h]
  refine ⟨a₀, fun a => ?_⟩
  split_ifs with ha
  · rw [ha, h1]
  · exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hrest a (Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩)

variable {Ω ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Commuting Switchboards are blends of deterministic records (H.8.4, linear-algebra core).** -/
theorem commuting_blend (u : Ω → OrthonormalBasis ι ℂ E) (b : OrthonormalBasis κ ℂ E)
    (hcomm : ∀ o i j, InnerProductSpace.rankOne ℂ (u o i) (u o i) ∘L
      InnerProductSpace.rankOne ℂ (b j) (b j) = InnerProductSpace.rankOne ℂ (b j) (b j) ∘L
      InnerProductSpace.rankOne ℂ (u o i) (u o i)) (φ : E) :
    ∃ f : κ → Ω → ι, (∀ o i, ‖⟪u o i, φ⟫_ℂ‖ ^ 2 =
        ∑ j, ‖⟪b j, φ⟫_ℂ‖ ^ 2 * (if f j o = i then 1 else 0)) ∧
      ∑ j, ‖⟪b j, φ⟫_ℂ‖ ^ 2 = ‖φ‖ ^ 2 := by
  set w : Ω → ι → κ → ℝ := fun o i j => ‖⟪u o i, b j⟫_ℂ‖ ^ 2
  have h01 : ∀ o i j, w o i j = 0 ∨ w o i j = 1 := by
    intro o i j
    rcases inner_eq_zero_or_norm_eq_one ((u o).orthonormal.1 i) (b.orthonormal.1 j)
      (hcomm o i j) with h | h
    · left; simp [w, h]
    · right; simp [w, h]
  have hsi : ∀ o j, ∑ i, w o i j = 1 := by
    intro o j
    have := (u o).sum_sq_norm_inner_right (b j)
    rw [b.orthonormal.1 j, one_pow] at this
    exact this
  have hsj : ∀ o i, ∑ j, w o i j = 1 := by
    intro o i
    have := b.sum_sq_norm_inner_right (u o i)
    rw [(u o).orthonormal.1 i, one_pow] at this
    simpa [w, norm_inner_symm] using this
  choose f hf using fun j o => exists_indicator (fun i => w o i j) (h01 o · j) (hsi o j)
  refine ⟨f, fun o i => ?_, b.sum_sq_norm_inner_right φ⟩
  obtain ⟨j₀, hj₀⟩ := exists_indicator (fun j => w o i j) (h01 o i) (hsj o i)
  have hexp : ⟪u o i, φ⟫_ℂ = ⟪u o i, b j₀⟫_ℂ * ⟪b j₀, φ⟫_ℂ := by
    rw [← b.sum_inner_mul_inner, Finset.sum_eq_single j₀]
    intro j _ hj
    have : w o i j = 0 := by simpa [hj] using hj₀ j
    have : ⟪u o i, b j⟫_ℂ = 0 := by simpa [w] using this
    rw [this, zero_mul]
    simp
  have hw : ∀ j, (if f j o = i then (1 : ℝ) else 0) = w o i j := fun j => by
    by_cases h : f j o = i
    · rw [hf j o i, ite_eq_left h, ite_eq_left h.symm]
    · rw [hf j o i, ite_eq_right h, ite_eq_right (Ne.symm h)]
  simp_rw [hw]
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hj₀ j, ite_eq_right hj, mul_zero])
    (by simp), hj₀ j₀, ite_eq_left rfl, mul_one, hexp, norm_mul, mul_pow]
  have : w o i j₀ = 1 := by simpa using hj₀ j₀
  simp only [w] at this
  rw [this, one_mul]

end PFUL.Switchboard
