import PFUL.KrausL2

/-!
# Choi kernels of local channels on countable alphabets

For a local channel with countably many Kraus operators, given by its Stinespring kernel
`V : O × Y → A → ℂ` (`A = I × X` the input with its ancilla, `Y` the Kraus index) with orthonormal
columns (`∑_y K_y† K_y = 1`), the **Choi kernel** is
`J (o, a) (o', a') = ∑_y V (o, y) a · conj V (o', y) a'`, the matrix entries
`⟨o, a| J |o', a'⟩` of `J = (Φ ⊗ id)(|Ω⟩⟨Ω|)` (unnormalised maximally entangled `|Ω⟩`). It is not
trace class for infinite alphabets, but it is a well-defined kernel:

* `hasSum_choiKernel`: the series over Kraus indices converges absolutely;
* `choiKernel_tp`: trace preservation, `∑_o J (o, a) (o, a') = δ_{a a'}`;
* `choiKernel_psd`: positivity, every finite section is positive semidefinite.

`valid_kraus_l2` takes exactly such a kernel `V` as input, so every channel specified by a Kraus
family (equivalently by a Choi kernel *together with* a factorisation `J = V V†` over a countable
Kraus index) is covered. The converse (every positive, trace-preserving Choi kernel on a countable
alphabet factors through a countable Kraus index) is not formalised.
-/

open scoped InnerProductSpace ComplexOrder ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

universe u

namespace PFUL.Countable

variable {O Y A : Type u} [DecidableEq A]

/-- Choi kernel of the channel with Stinespring kernel `V`. -/
noncomputable def choiKernel (V : O × Y → A → ℂ) (p q : O × A) : ℂ :=
  ∑' y, V (p.1, y) p.2 * star (V (q.1, y) q.2)

theorem summable_mul_star_of_sq {R : Type*} {f g : R → ℂ} (hf : Summable fun r => ‖f r‖ ^ 2)
    (hg : Summable fun r => ‖g r‖ ^ 2) : Summable fun r => f r * star (g r) := by
  refine Summable.of_norm_bounded (g := fun r => ‖f r‖ ^ 2 + ‖g r‖ ^ 2) (hf.add hg) fun r => ?_
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖f r‖ - ‖g r‖), norm_nonneg (f r), norm_nonneg (g r)]

theorem summable_sq_of_hiso {V : O × Y → A → ℂ}
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0)) (a : A) :
    Summable fun r : O × Y => ‖V r a‖ ^ 2 := by
  have h := hiso a a
  simp_rw [star_mul_self_eq] at h
  exact Complex.summable_ofReal.1 h.summable

theorem hasSum_choiKernel {V : O × Y → A → ℂ}
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (p q : O × A) :
    HasSum (fun y => V (p.1, y) p.2 * star (V (q.1, y) q.2)) (choiKernel V p q) := by
  refine Summable.hasSum ?_
  have hs := fun a => summable_sq_of_hiso hiso a
  exact summable_mul_star_of_sq ((hs p.2).comp_injective (fun y y' h => by simpa using h) :
      Summable fun y => ‖V (p.1, y) p.2‖ ^ 2)
    ((hs q.2).comp_injective (fun y y' h => by simpa using h) :
      Summable fun y => ‖V (q.1, y) q.2‖ ^ 2)

/-- **Trace preservation of the Choi kernel:** `∑_o J (o, a) (o, a') = δ_{a a'}`. -/
theorem choiKernel_tp {V : O × Y → A → ℂ}
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (a a' : A) :
    HasSum (fun o => choiKernel V (o, a) (o, a')) (if a' = a then 1 else 0) := by
  have h := hiso a' a
  have hsum : Summable fun r : O × Y => V r a * star (V r a') :=
    summable_mul_star_of_sq (summable_sq_of_hiso hiso a) (summable_sq_of_hiso hiso a')
  have h2 : HasSum (fun r : O × Y => V r a * star (V r a')) (if a' = a then 1 else 0) := by
    convert h using 1; funext r; ring
  exact (h2.unique hsum.hasSum ▸ hsum.hasSum).prod_fiberwise fun o =>
    hasSum_choiKernel hiso (o, a) (o, a') |>.congr_fun (fun _ => rfl) |> id

/-- **Positivity of the Choi kernel:** every finite section is positive semidefinite. -/
theorem choiKernel_psd {V : O × Y → A → ℂ}
    (hiso : ∀ a a', HasSum (fun r => star (V r a) * V r a') (if a = a' then 1 else 0))
    (s : Finset (O × A)) (c : O × A → ℂ) :
    0 ≤ ∑ p ∈ s, ∑ q ∈ s, star (c p) * choiKernel V p q * c q := by
  have hterm : ∀ p q, HasSum (fun y => star (c p) * (V (p.1, y) p.2 * star (V (q.1, y) q.2)) * c q)
      (star (c p) * choiKernel V p q * c q) := fun p q =>
    ((hasSum_choiKernel hiso p q).mul_left (star (c p))).mul_right (c q)
  have htot := hasSum_sum fun p (_ : p ∈ s) => hasSum_sum fun q (_ : q ∈ s) => hterm p q
  have hy : ∀ y, ∑ p ∈ s, ∑ q ∈ s, star (c p) * (V (p.1, y) p.2 * star (V (q.1, y) q.2)) * c q =
      star (∑ p ∈ s, c p * star (V (p.1, y) p.2)) * (∑ p ∈ s, c p * star (V (p.1, y) p.2)) := by
    intro y
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [star_mul', star_star]; ring
  simp_rw [hy] at htot
  rw [← htot.tsum_eq]
  exact tsum_nonneg fun y => by rw [star_mul_self_eq]; exact Complex.zero_le_real.2 (by positivity)

end PFUL.Countable

