/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Infinitely many parties, continuous processes: exclusivity ⇒ process function

Arbitrary index type `ι`, finite nonempty discrete output alphabets, discrete input alphabets.
If every coordinate `s ↦ w s k` is continuous (product topology) and `w` is exclusive, then
every intervention has exactly one fixed point. Proof: for a finite party set `T` and any
background `t`, the restriction `u ↦ (f ∘ w)(u ⊔ t)|_T` is exclusive on finitely many parties,
so by `exclusive_iff_pf` it has a fixed point; hence the closed sets
`{s | f k (w s k) = s k}` have the finite intersection property in the compact space `∀ k, O k`.
-/
import PFUL.GeneralAlphabets

namespace PFUL.Infinite

variable {ι : Type*} {I O : ι → Type*}

theorem pf_of_exclusive_continuous
    [∀ k, TopologicalSpace (O k)] [∀ k, DiscreteTopology (O k)] [∀ k, Finite (O k)]
    [∀ k, Nonempty (O k)]
    [∀ k, TopologicalSpace (I k)] [∀ k, DiscreteTopology (I k)]
    (w : (∀ k, O k) → (∀ k, I k)) (hc : ∀ k, Continuous fun s => w s k)
    (hex : FiniteBox.Exclusive w) (f : ∀ k, I k → O k) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  refine (existsUnique_of_exists_of_unique ?_ ?_)
  · let C : ι → Set (∀ k, O k) := fun k => {s | f k (w s k) = s k}
    have hC : ∀ k, IsClosed (C k) := fun k =>
      isClosed_eq ((continuous_of_discreteTopology (f := f k)).comp (hc k)) (continuous_apply k)
    have hfin : ∀ T : Finset ι, (Set.univ ∩ ⋂ k ∈ T, C k).Nonempty := by
      intro T
      obtain ⟨t⟩ : Nonempty (∀ k, O k) := inferInstance
      let mg : (∀ k : T, O k) → (∀ k, O k) := fun u j => if h : j ∈ T then u ⟨j, h⟩ else t j
      let G : (∀ k : T, O k) → (∀ k : T, O k) := fun u k => f k (w (mg u) k)
      have hG : FiniteBox.Exclusive G := by
        intro u u' hne
        have hm : mg u ≠ mg u' := by
          intro h; apply hne; funext ⟨j, hj⟩
          have := congrFun h j; simpa [mg, hj] using this
        obtain ⟨k, hk, hw⟩ := hex _ _ hm
        have hkT : k ∈ T := by
          by_contra hn; exact hk (by simp [mg, hn])
        refine ⟨⟨k, hkT⟩, ?_, ?_⟩
        · intro h; apply hk; simp [mg, hkT, h]
        · simp only [G, hw]
      obtain ⟨u, hu, -⟩ := (PFUL.General.exclusive_iff_pf G).1 hG (fun _ => id)
      refine ⟨mg u, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter]
      intro k hk
      have := hu ⟨k, hk⟩
      simp only [id, G] at this
      show f k (w (mg u) k) = mg u k
      simp only [mg, hk, dif_pos]; exact this
    obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty C hC hfin
    exact ⟨s, fun k => Set.mem_iInter.1 hs k⟩
  · intro s s' hs hs'
    by_contra hne
    obtain ⟨k, hk, hw⟩ := hex s s' hne
    exact hk (by rw [← hs k, ← hs' k, hw])

end PFUL.Infinite

#print axioms PFUL.Infinite.pf_of_exclusive_continuous
