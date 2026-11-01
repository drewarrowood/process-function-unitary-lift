import Mathlib

/-! Counting half of Theorem N.1: if every local map `f` has at most one fixed point
of `s ↦ f (w s)`, then every `f` has exactly one (i.e. `w` is a process function).
Uses Σ_f N(f) = #f, proved by explicit relabelling bijections. -/

namespace PFUL.ExclusivityCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
  [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]

/-- number of `f` with prescribed values `s` at input point `a`. -/
lemma card_out_relabel (a : ∀ k, I k) (s t : ∀ k, O k) :
    Fintype.card {f : ∀ k, I k → O k // ∀ k, f k (a k) = s k}
      = Fintype.card {f : ∀ k, I k → O k // ∀ k, f k (a k) = t k} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv
    (Equiv.piCongrRight fun k => Equiv.arrowCongr (Equiv.refl _) (Equiv.swap (s k) (t k))) ?_)
  intro f
  refine forall_congr' fun k => ?_
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, CompTriple.comp_eq]
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

lemma card_in_relabel (a b : ∀ k, I k) (s : ∀ k, O k) :
    Fintype.card {f : ∀ k, I k → O k // ∀ k, f k (a k) = s k}
      = Fintype.card {f : ∀ k, I k → O k // ∀ k, f k (b k) = s k} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv
    (Equiv.piCongrRight fun k => Equiv.arrowCongr (Equiv.swap (a k) (b k)) (Equiv.refl _)) ?_)
  intro f
  refine forall_congr' fun k => ?_
  simp [Pi.map_apply, Equiv.arrowCongr_apply, Equiv.symm_swap, Equiv.swap_apply_right]

variable (w : (∀ k, O k) → ∀ k, I k)

/-- fixed points of the loop closed by `f`. -/
def N (f : ∀ k, I k → O k) : ℕ :=
  (Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k).card

theorem sum_N_eq_card (a0 : ∀ k, I k) (s0 : ∀ k, O k) :
    ∑ f, N w f = Fintype.card (∀ k, I k → O k) := by
  classical
  set C := Fintype.card {f : ∀ k, I k → O k // ∀ k, f k (a0 k) = s0 k}
  have hK : ∀ s : ∀ k, O k,
      (Finset.univ.filter fun f : ∀ k, I k → O k => ∀ k, f k (w s k) = s k).card = C := by
    intro s
    rw [← Fintype.card_subtype, card_in_relabel (w s) a0 s, card_out_relabel a0 s s0]
  have h1 : ∑ f, N w f = Fintype.card (∀ k, O k) * C := by
    unfold N
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.card_filter, hK]
    simp [Finset.card_univ]
  have h2 : Fintype.card (∀ k, I k → O k) = Fintype.card (∀ k, O k) * C := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun f : ∀ k, I k → O k => fun k => f k (a0 k)) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    have : ∀ t : ∀ k, O k, (Finset.univ.filter fun f : ∀ k, I k → O k =>
        (fun k => f k (a0 k)) = t).card = C := by
      intro t
      rw [show (Finset.univ.filter fun f : ∀ k, I k → O k => (fun k => f k (a0 k)) = t)
          = Finset.univ.filter (fun f : ∀ k, I k → O k => ∀ k, f k (a0 k) = t k) by
            ext f; simp [funext_iff]]
      rw [← Fintype.card_subtype, card_out_relabel a0 t s0]
    simp_rw [this]
    simp [Finset.card_univ]
  rw [h1, h2]

/-- Exclusivity (at most one fixed point for every `f`) implies the process-function
property (exactly one fixed point for every `f`). -/
theorem exclusive_imp_pf (a0 : ∀ k, I k) (s0 : ∀ k, O k)
    (hex : ∀ f, N w f ≤ 1) : ∀ f, N w f = 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨f, hf⟩ := h
  have hlt : ∑ g, N w g < ∑ _g : (∀ k, I k → O k), 1 :=
    Finset.sum_lt_sum (fun g _ => hex g) ⟨f, Finset.mem_univ _, lt_of_le_of_ne (hex f) hf⟩
  rw [sum_N_eq_card w a0 s0] at hlt
  simp at hlt

theorem exclusive_imp_existsUnique (a0 : ∀ k, I k) (s0 : ∀ k, O k)
    (hex : ∀ f, N w f ≤ 1) (f : ∀ k, I k → O k) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  have := exclusive_imp_pf w a0 s0 hex f
  unfold N at this
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp this
  refine ⟨s, ?_, fun s' hs' => ?_⟩
  · have : s ∈ ({s} : Finset _) := Finset.mem_singleton_self s
    rw [← hs] at this; simpa using this
  · have : s' ∈ (Finset.univ.filter fun s : ∀ k, O k => ∀ k, f k (w s k) = s k) := by simpa using hs'
    rw [hs] at this; simpa using this

end PFUL.ExclusivityCount
