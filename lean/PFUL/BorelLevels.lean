/-
# Σ⁰₂ and Π⁰₂ counterexamples (intermediate-classes note, §10)

* `zfcF_coord_sigma02` : every coordinate set `{s | zfcF s k = true}` is `F_σ` (Σ⁰₂).
* `zfcD` : the dual `s ↦ ¬ zfcF (¬ s)` is exclusive and fixed-point free, and every coordinate
  set is `G_δ` (Π⁰₂).
So neither one-sided level suffices for a fixed point; the open case is exactly Δ⁰₂ = class 1
for `Bool`-valued coordinates on Cantor space.
-/
import PFUL.BaireClasses

open Set

namespace PFUL.Infinite

lemma zv_continuous (k : ℕ) : Continuous (zv k) := by
  cases k with
  | zero => exact continuous_const
  | succ k => exact continuous_apply k

theorem zfcF_coord_sigma02 (k : ℕ) : ∃ C : ℕ → Set (ℕ → Bool), (∀ N, IsClosed (C N)) ∧
    {s | zfcF s k = true} = ⋃ N, C N := by
  classical
  obtain ⟨C, hC, hE⟩ := finSupp_isFσ
  refine ⟨fun N => C N ∩ {s | zv k s = true}, fun N =>
    (hC N).inter (isClosed_eq (zv_continuous k) continuous_const), ?_⟩
  rw [← iUnion_inter, ← hE]
  ext s
  simp only [mem_ofPred_eq, mem_inter_iff, zfcF_eq_ite s k]
  by_cases h : FinSupp s
  · rw [ite_t h]; simp [h]
  · rw [ite_f h]; simp [h]

/-- The dual of `zfcF` (negate input and output). -/
noncomputable def zfcD (s : ℕ → Bool) : ℕ → Bool := fun k => !(zfcF (fun j => !s j) k)

theorem zfcD_ne (s : ℕ → Bool) : zfcD s ≠ s := by
  intro h
  apply zfcF_ne (fun j => !s j)
  funext k
  have := congrFun h k
  simp only [zfcD] at this
  rw [← this]; simp

theorem zfcD_exclusive : Exclusive zfcD := by
  intro s t hne
  have hne' : (fun j => !s j) ≠ fun j => !t j := fun h => hne (funext fun j => by
    simpa using congrFun h j)
  obtain ⟨k, hk, hw⟩ := zfcF_exclusive _ _ hne'
  exact ⟨k, fun h => hk (by simp [h]), by simp only [zfcD, hw]⟩

theorem zfcD_coord_pi02 (k : ℕ) : IsGδ {s | zfcD s k = true} := by
  obtain ⟨C, hC, hE⟩ := zfcF_coord_sigma02 k
  have hneg : Continuous fun s : ℕ → Bool => fun j => !s j :=
    continuous_pi fun j => continuous_of_discreteTopology.comp (continuous_apply j)
  have : {s | zfcD s k = true} = ⋂ N, ((fun s : ℕ → Bool => fun j => !s j) ⁻¹' C N)ᶜ := by
    ext s
    have h := congrArg (fun A => (fun j => !s j) ∈ A) hE
    simp only [mem_ofPred_eq, mem_iUnion, eq_iff_iff] at h
    simp only [zfcD, mem_ofPred_eq, mem_iInter, mem_compl_iff, mem_preimage, Bool.not_eq_true',
      ← not_exists, ← h]
    simp
  rw [this]
  exact IsGδ.iInter_of_isOpen fun N => ((hC N).preimage hneg).isOpen_compl

end PFUL.Infinite

#print axioms PFUL.Infinite.zfcF_coord_sigma02
#print axioms PFUL.Infinite.zfcD_ne
#print axioms PFUL.Infinite.zfcD_exclusive
#print axioms PFUL.Infinite.zfcD_coord_pi02
