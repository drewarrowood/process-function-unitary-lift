import PFUL.ConjugateBijection

open Set
namespace PFUL.Infinite

/-- A finite global image reduces arbitrarily many Boolean parties to finitely many
coordinate patterns. No continuity, countability of parties, or exceptional set is used. -/
theorem exists_fixed_of_finite_global_range {ι : Type*}
    {F : (ι → Bool) → (ι → Bool)} (hex : Exclusive F) (hfin : (Set.range F).Finite) :
    ∃ x, F x = x := by
  classical
  let R := Set.range F
  let : Fintype R := hfin.fintype
  let pattern : ι → (R → Bool) := fun k r => r.val k
  let J := Set.range pattern
  let : Fintype J := Fintype.ofFinite J
  let rep : J → ι := fun j => Classical.choose j.property
  have hrep : ∀ j : J, pattern (rep j) = j.val := fun j => Classical.choose_spec j.property
  let glue : (J → Bool) → ι → Bool := fun a k => a ⟨pattern k, mem_range_self k⟩
  have hglue_rep : ∀ a (j : J), glue a (rep j) = a j := by
    intro a j
    dsimp [glue]
    congr 1
    exact Subtype.ext (hrep j)
  have hglue_inj : Function.Injective glue := fun a b h => funext fun j => by
    have := congrFun h (rep j)
    simpa only [hglue_rep] using this
  let W : (J → Bool) → (J → Bool) := fun a j => F (glue a) (rep j)
  have hpattern : ∀ a k, W a ⟨pattern k, mem_range_self k⟩ = F (glue a) k := by
    intro a k
    have hp := congrFun (hrep (⟨pattern k, mem_range_self k⟩ : J))
      (⟨F (glue a), mem_range_self (glue a)⟩ : R)
    exact hp
  have hW : Exclusive W := by
    intro a b hab
    have hg : glue a ≠ glue b := fun h => hab (hglue_inj h)
    obtain ⟨k, hk, hw⟩ := hex (glue a) (glue b) hg
    refine ⟨⟨pattern k, mem_range_self k⟩, hk, ?_⟩
    rw [hpattern, hpattern]
    exact hw
  obtain ⟨a, ha⟩ := exists_fixed_of_exclusive hW
  refine ⟨glue a, funext fun k => ?_⟩
  have h := congrFun ha (⟨pattern k, mem_range_self k⟩ : J)
  simpa only [hpattern] using h

/-- Finite global image suffices for full process-function consistency, with any
party set and arbitrary input alphabets, provided the local outputs are Boolean. -/
theorem isProcessFunction_of_exclusive_finite_global_range {ι : Type*} {I : ι → Type*}
    {w : (ι → Bool) → (∀ k, I k)} (hex : Exclusive w) (hfin : (Set.range w).Finite) :
    IsProcessFunction w := by
  intro f
  let H : (ι → Bool) → (ι → Bool) := fun s k => f k (w s k)
  have hH : Exclusive H := by
    intro s t hst
    obtain ⟨k, hk, hw⟩ := hex s t hst
    exact ⟨k, hk, by simp only [H, hw]⟩
  have hHfin : (Set.range H).Finite :=
    (hfin.image (fun v k => f k (v k))).subset (by
      rintro _ ⟨s, rfl⟩
      exact mem_image_of_mem _ (mem_range_self s))
  obtain ⟨s, hs⟩ := exists_fixed_of_finite_global_range hH hHfin
  refine ⟨s, fun k => congrFun hs k, fun t ht => ?_⟩
  exact fixed_unique hex f ht (fun k => congrFun hs k)

end PFUL.Infinite

#print axioms PFUL.Infinite.exists_fixed_of_finite_global_range
#print axioms PFUL.Infinite.isProcessFunction_of_exclusive_finite_global_range
