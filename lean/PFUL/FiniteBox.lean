/-
Copyright (c) 2026 Drew Lamarr Arrowood. All rights reserved.
Released under Apache 2.0 license.

# Exclusivity and fixed points on arbitrary (e.g. countably infinite) alphabets

No finiteness of the alphabets is assumed. If `w` satisfies pairwise exclusivity, then
* every intervention has at most one fixed point (`fixed_unique`);
* an intervention has a fixed point as soon as `s ↦ f (w s)` maps some nonempty finite box
  `∏ O' k` into itself (`existsUnique_of_box`): restrict to the box and use the finite
  counting theorem `ExclusivityCount.exclusive_imp_existsUnique`;
* in particular, if every `w k` has finite range, `w` is a process function
  (`pf_of_exclusive_finiteRange`).
-/
import PFUL.ExclusivityCount

set_option linter.unusedSectionVars false

namespace PFUL.FiniteBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I O : ι → Type*}
  [∀ k, DecidableEq (I k)] [∀ k, DecidableEq (O k)]

/-- Pairwise exclusivity. -/
def Exclusive (w : (∀ k, O k) → (∀ k, I k)) : Prop :=
  ∀ s s' : ∀ k, O k, s ≠ s' → ∃ k, s k ≠ s' k ∧ w s k = w s' k

lemma fixed_unique {w : (∀ k, O k) → (∀ k, I k)} (hex : Exclusive w) (f : ∀ k, I k → O k)
    {s s' : ∀ k, O k} (hs : ∀ k, f k (w s k) = s k) (hs' : ∀ k, f k (w s' k) = s' k) :
    s = s' := by
  by_contra hne
  obtain ⟨k, hk, he⟩ := hex s s' hne
  exact hk (by rw [← hs k, ← hs' k, he])

/-- **Finite-box lemma.** Exclusivity plus a nonempty finite box invariant under `s ↦ f (w s)`
gives a unique fixed point. -/
theorem existsUnique_of_box (w : (∀ k, O k) → (∀ k, I k)) (hex : Exclusive w)
    (f : ∀ k, I k → O k) (B : ∀ k, Finset (O k)) (hB : ∀ k, (B k).Nonempty)
    (hinv : ∀ s : ∀ k, O k, (∀ k, s k ∈ B k) → ∀ k, f k (w s k) ∈ B k) :
    ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  -- the box as a finset of strings, and the finite input sets T k
  let box : Finset (∀ k, O k) := Fintype.piFinset B
  let T : ∀ k, Finset (I k) := fun k => box.image (fun s => w s k)
  let O' : ι → Type _ := fun k => {o // o ∈ B k}
  let I' : ι → Type _ := fun k => {i // i ∈ T k}
  have memT : ∀ (s : ∀ k, O' k) k, w (fun j => (s j).1) k ∈ T k := by
    intro s k
    exact Finset.mem_image.2 ⟨fun j => (s j).1, Fintype.mem_piFinset.2 fun j => (s j).2, rfl⟩
  let w' : (∀ k, O' k) → ∀ k, I' k := fun s k => ⟨w (fun j => (s j).1) k, memT s k⟩
  have memB : ∀ k (i : I' k), f k i.1 ∈ B k := by
    intro k i
    obtain ⟨s, hs, hsi⟩ := Finset.mem_image.1 i.2
    rw [← hsi]
    exact hinv s (fun j => Fintype.mem_piFinset.1 hs j) k
  let f' : ∀ k, I' k → O' k := fun k i => ⟨f k i.1, memB k i⟩
  have hex' : ∀ g : ∀ k, I' k → O' k, ExclusivityCount.N w' g ≤ 1 := by
    intro g
    unfold ExclusivityCount.N
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    have hab' : (fun j => (a j).1) ≠ (fun j => (b j).1) := by
      intro h; apply hab; funext j; exact Subtype.ext (congrFun h j)
    obtain ⟨k, hk, he⟩ := hex _ _ hab'
    apply hk
    have e1 := congrArg Subtype.val (ha k)
    have e2 := congrArg Subtype.val (hb k)
    have : w' a k = w' b k := Subtype.ext he
    rw [← e1, ← e2, this]
  have a0 : ∀ k, I' k := fun k =>
    w' (fun j => ⟨(hB j).choose, (hB j).choose_spec⟩) k
  have s0 : ∀ k, O' k := fun k => ⟨(hB k).choose, (hB k).choose_spec⟩
  obtain ⟨s', hs', -⟩ := ExclusivityCount.exclusive_imp_existsUnique w' a0 s0 hex' f'
  refine ⟨fun j => (s' j).1, fun k => congrArg Subtype.val (hs' k), fun t ht => ?_⟩
  exact fixed_unique hex f ht (fun k => congrArg Subtype.val (hs' k))

/-- **Exclusivity + finite ranges ⇒ process function**, on arbitrary alphabets. -/
theorem pf_of_exclusive_finiteRange (w : (∀ k, O k) → (∀ k, I k)) (hex : Exclusive w)
    [∀ k, Nonempty (O k)] (hfin : ∀ k, (Set.range fun s => w s k).Finite)
    (f : ∀ k, I k → O k) : ∃! s : ∀ k, O k, ∀ k, f k (w s k) = s k := by
  classical
  let o0 : ∀ k, O k := fun k => Classical.arbitrary _
  let B : ∀ k, Finset (O k) := fun k => insert (o0 k) ((hfin k).toFinset.image (f k))
  refine existsUnique_of_box w hex f B (fun k => ⟨o0 k, Finset.mem_insert_self _ _⟩) ?_
  intro s _ k
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨w s k, (hfin k).mem_toFinset.2 ⟨s, rfl⟩, rfl⟩)

/-- Conversely, a fixed point gives a one-point invariant box: for exclusive `w`, an intervention
has a fixed point iff `s ↦ f (w s)` has a nonempty finite invariant box. -/
theorem box_of_fixed (w : (∀ k, O k) → (∀ k, I k)) (f : ∀ k, I k → O k) (s : ∀ k, O k)
    (hs : ∀ k, f k (w s k) = s k) :
    ∀ t : ∀ k, O k, (∀ k, t k ∈ ({s k} : Finset (O k))) → ∀ k, f k (w t k) ∈ ({s k} : Finset _) := by
  intro t ht k
  have : t = s := funext fun j => Finset.mem_singleton.1 (ht j)
  subst this
  simp [hs k]

end PFUL.FiniteBox
