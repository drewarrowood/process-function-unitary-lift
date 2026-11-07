import PFUL.ConjugateBijection

namespace PFUL.Infinite

/-- A finite continuous exclusive map invalidating the tempting maximal-postfixed
argument for semicontinuous maps. Coordinates are ordered false < true. -/
def postfixedProbe (s : Fin 2 → Bool) (k : Fin 2) : Bool :=
  if k = 0 then !(s 1) else true

def postfixedBad : Fin 2 → Bool := fun k => decide (k = 0)

set_option maxRecDepth 10000 in
theorem maximal_postfixed_need_not_be_fixed :
    Exclusive postfixedProbe ∧
    (∀ k, postfixedBad k ≤ postfixedProbe postfixedBad k) ∧
    postfixedProbe postfixedBad ≠ postfixedBad ∧
    (∀ y : Fin 2 → Bool, (∀ k, postfixedBad k ≤ y k) →
      (∀ k, y k ≤ postfixedProbe y k) → y = postfixedBad) := by
  unfold Exclusive
  decide

end PFUL.Infinite

#print axioms PFUL.Infinite.maximal_postfixed_need_not_be_fixed
