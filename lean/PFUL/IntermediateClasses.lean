/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Between continuous and Borel: what is known about exclusive ⇒ PF

* `zfcF_not_continuousAt`: the ZFC counterexample is continuous at no point (so it is not of
  Baire class 1, by Baire's theorem on points of continuity; that step is paper-only).
* `exists_fixed_of_monotone`: a monotone self-map of `ι → Bool` always has a fixed point
  (Knaster–Tarski), so no monotone map is a counterexample.
* `pf_of_exclusive_finitary`: if each coordinate of `w` depends on finitely many outputs, then
  exclusive ⇒ PF (such `w` is continuous; `pf_of_exclusive_continuous`).
-/
import PFUL.ZFCCounterexample
import PFUL.InfiniteCompact
import PFUL.ConjugateBijection

open Set Filter Topology

namespace PFUL.Infinite

/-- The ZFC counterexample is discontinuous at every point (already its coordinate 0 is). -/
theorem zfcF_not_continuousAt (s : ℕ → Bool) : ¬ ContinuousAt zfcF s := by
  classical
  intro hc
  have h0 : ContinuousAt (fun x => zfcF x 0) s := (continuous_apply 0).continuousAt.comp hc
  -- approximants agreeing with `s` below `n`, constant `c` from `n` on
  let ap : Bool → ℕ → ℕ → Bool := fun c n k => if k < n then s k else c
  have hlim : ∀ c, Tendsto (ap c) atTop (𝓝 s) := fun c => by
    rw [tendsto_pi_nhds]; intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [ap, hn]
  have hfin : ∀ n, FinSupp (ap false n) := fun n =>
    (finite_lt_nat n).subset fun k hk => by
      by_contra h; simp only [mem_ofPred_eq, not_lt] at h hk; simp [ap, not_lt.2 h] at hk
  have hinf : ∀ n, ¬ FinSupp (ap true n) := fun n hF => by
    obtain ⟨N, hN⟩ := bound_of_finSupp hF
    have := hN (max n N) (le_max_right _ _); simp [ap] at this
  by_cases hs : FinSupp s
  · have hv : zfcF s 0 = true := by rw [zfcF_fin hs]
    have t := h0.tendsto.comp (hlim true)
    rw [hv] at t
    have : ∀ n, (fun x => zfcF x 0) (ap true n) = false := fun n => zfcF_inf (hinf n) 0
    have t' : Tendsto (fun _ : ℕ => false) atTop (𝓝 true) := t.congr this
    exact Bool.false_ne_true (tendsto_nhds_unique tendsto_const_nhds t')
  · have hv : zfcF s 0 = false := zfcF_inf hs 0
    have t := h0.tendsto.comp (hlim false)
    rw [hv] at t
    have : ∀ n, (fun x => zfcF x 0) (ap false n) = true := fun n => by
      show zfcF (ap false n) 0 = true; rw [zfcF_fin (hfin n)]
    have t' : Tendsto (fun _ : ℕ => true) atTop (𝓝 false) := t.congr this
    exact Bool.false_ne_true (tendsto_nhds_unique t' tendsto_const_nhds)

/-- Knaster–Tarski: every monotone self-map of `ι → Bool` has a fixed point. -/
theorem exists_fixed_of_monotone {ι : Type*} {F : (ι → Bool) → (ι → Bool)} (hF : Monotone F) :
    ∃ s, F s = s :=
  ⟨OrderHom.lfp ⟨F, hF⟩, OrderHom.map_lfp ⟨F, hF⟩⟩

/-- **Finitary maps.** If each coordinate of `w` factors through finitely many outputs, then
exclusive ⇒ every intervention has exactly one fixed point. -/
theorem pf_of_exclusive_finitary {ι : Type*} {I O : ι → Type*}
    [∀ k, TopologicalSpace (O k)] [∀ k, DiscreteTopology (O k)] [∀ k, Finite (O k)]
    [∀ k, Nonempty (O k)] [∀ k, TopologicalSpace (I k)] [∀ k, DiscreteTopology (I k)]
    (w : (∀ k, O k) → (∀ k, I k)) (T : ι → Finset ι)
    (g : ∀ k, (∀ j : T k, O j) → I k) (hg : ∀ s k, w s k = g k (fun j => s j))
    (hex : FiniteBox.Exclusive w) (f : ∀ k, I k → O k) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  refine pf_of_exclusive_continuous w (fun k => ?_) hex f
  have : (fun s => w s k) = g k ∘ fun s (j : T k) => s j := funext fun s => hg s k
  rw [this]
  exact continuous_of_discreteTopology.comp (continuous_pi fun j => continuous_apply _)

/-- **Splitting lemma.** If freezing a finite set `T` of parties to any values `b` always leaves a
consistent history for the remaining parties, then an exclusive `F` has a fixed point. -/
theorem exists_fixed_of_frozen {ι : Type*} {F : (ι → Bool) → (ι → Bool)} (hex : Exclusive F)
    (T : Finset ι)
    (h : ∀ b : ι → Bool, ∃ x : ι → Bool, (∀ k ∈ T, x k = b k) ∧ ∀ k, k ∉ T → F x k = x k) :
    ∃ s, F s = s := by
  classical
  choose x hxT hxF using h
  let ext : (T → Bool) → ι → Bool := fun β k => if hk : k ∈ T then β ⟨k, hk⟩ else false
  let R : (T → Bool) → (T → Bool) := fun β k => F (x (ext β)) k
  have hR : Exclusive R := by
    intro β β' hne
    have hxne : x (ext β) ≠ x (ext β') := by
      intro heq
      apply hne; funext ⟨k, hk⟩
      have h1 := hxT (ext β) k hk; have h2 := hxT (ext β') k hk
      simp only [ext, hk, ↓reduceDIte] at h1 h2
      rw [← h1, ← h2, heq]
    obtain ⟨j, hj, hF⟩ := hex _ _ hxne
    have hjT : j ∈ T := by
      by_contra hjT; exact hj (by rw [← hxF _ j hjT, ← hxF _ j hjT, hF])
    refine ⟨⟨j, hjT⟩, ?_, hF⟩
    intro hb; apply hj
    rw [hxT _ j hjT, hxT _ j hjT]; simp only [ext, hjT, ↓reduceDIte, hb]
  obtain ⟨β, hβ⟩ := exists_fixed_of_exclusive hR
  refine ⟨x (ext β), funext fun k => ?_⟩
  by_cases hk : k ∈ T
  · have := congrFun hβ ⟨k, hk⟩
    simp only [R] at this
    rw [this, hxT _ k hk]; simp [ext, hk]
  · exact hxF _ k hk

end PFUL.Infinite

#print axioms PFUL.Infinite.zfcF_not_continuousAt
#print axioms PFUL.Infinite.exists_fixed_of_monotone
#print axioms PFUL.Infinite.pf_of_exclusive_finitary
#print axioms PFUL.Infinite.exists_fixed_of_frozen
