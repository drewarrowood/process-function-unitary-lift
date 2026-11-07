# Perfect nowhere-dense discontinuity sets: a padding construction (2026-11-07)

Exclusive (as in InfiniteParties.lean/FiniteBox.lean): for all s ≠ s' there is k with s k ≠ s' k and F s k = F s' k.

P := {s ∈ 2^ℕ : s(2j+1)=0 ∀j} is closed, perfect and has empty interior.
pad G (s)(k) := G(ev s)(k/2) if s ∈ P and k even, else 0, where (ev s)(j) = s(2j).

Lemmas (all checked in Lean, PerfectPad.lean, axioms propext/choice/Quot.sound, no sorry):
1. G exclusive ⇒ pad G exclusive. If both points are in P, use G's witness at 2j. If exactly one is in P, take an odd coordinate where the other point is 1: both outputs are 0 there. If neither is in P, both outputs are 0, so any differing coordinate works.
2. G has no fixed point ⇒ pad G has no fixed point. On P the even part would be a fixed point of G. Off P, some odd input is 1 but the output there is 0.
3. pad G = 0 on the open set Pᶜ, so it is continuous at every point off P.
4. BaireOne(pad G) ⇔ BaireOne G. (⇒) restrict along the continuous embedding emb: 2^ℕ → P. (⇐) use f_n(s)(k) = [s(2j+1)=0 ∀ j<n] ∧ [k even] ∧ g_n(ev s)(k/2).

Theorem A: pad zfcF is exclusive, has no fixed point, is constant off a closed perfect nowhere-dense set, is continuous off it, and is not Baire one.
So continuity off a perfect nowhere-dense set does not force a fixed point. It also shows that L269–272 (exists_fixed_of_closure_finite_diff) really needs S to be countable: here the map is constant off an uncountable closed S.

Theorem B (reduction): from any exclusive, fixed-point-free Baire-one G we get pad G, which is also exclusive, fixed-point-free and Baire one, and is in addition constant off P. The restricted problem is a special case of the full one. So the two are equivalent:
"exclusive + Baire one ⇒ fixed point" holds iff it holds for maps continuous (even constant) off a closed perfect nowhere-dense set.
Assuming that discontinuities lie in a perfect nowhere-dense set gives no traction on its own. The class-1 question is unchanged.

## Integrated (labels L-277–L-285)

The statements above are in `lean/PFUL/PerfectPad.lean` and are cited from `paper/lift.md` (L.4(e)) and retold, as illustrations, in `paper/graded.md` §128. The technical note is the source of truth for the claims; the stories are not.

Labels: `isClosed_P` L-277, `interior_P` L-278, `perfect_P` L-279, `pad_exclusive` L-280, `pad_ne` L-281, `pad_continuousAt` L-282, `baireOne_pad_iff` L-283, `exists_exclusive_fpf_const_off_perfect` L-284, `reduction` L-285.

Continuity off P puts every discontinuity inside P. Equality of the discontinuity set with P is not proved and is not asserted. The Baire-one equivalence reduces the restricted fixed-point question to the full Baire-class-1 question. The countable-closed conjecture remains open. Other questions in the note remain open as well.
