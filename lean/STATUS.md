# Lean status (Lean 4.34.1, Mathlib v4.34.1)

## Main result: PFUL/UnitaryLift.lean (uses Mathlib)
- `PFUL.IsProcessFunction w`: for every `f : ∀ k, I k → O k`, there is exactly one `s` with `f k (w s k) = s k` for all k.
- `PFUL.exclusivity`: the lemma, derived here and not assumed. For s ≠ s' there is a k with s k ≠ s' k and w s k = w s' k.
- `PFUL.induced`: M (s,y) (e,x) = ∏ k, V k (s k, y k) (w s k + e k, x k).
- `PFUL.induced_mul_conjTranspose`: if w is a process function and V k * (V k)ᴴ = 1 for every k, then M * Mᴴ = 1. This holds over any field with a star operation (`Field 𝕜`, `StarRing 𝕜`), for any finite set of parties `ι`, finite input groups `I k`, finite output sets `O k`, and finite local ancillas `X k`, `Y k`. Input and output sizes may differ.
- `PFUL.induced_mul_conjTranspose_complex`: the same theorem with 𝕜 = ℂ.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no custom axioms, no `native_decide`.
- Not in Lean: "M Mᴴ = 1 and M square ⇒ Mᴴ M = 1". The index types differ, so the theorem is stated as orthonormal rows. Squareness is the dimension count in paper Appendix B.

## Legacy Mathlib-free files (library `Legacy`)

Build: `cd lean && lake build`. Every file compiles. There is no `sorry`, `admit` or `axiom` declaration. Files that use `native_decide` also depend on the compiler-trust axiom `Lean.ofReduceBool`: Full.lean (`hadamard_rows_orthogonal` only), Gaps.lean (`hadamard_rows`, `trace_identity_ancilla`), Cancel.lean (finite checks), and StinespringBoundary.lean (`closed_not_every_w`).

### Proved (no hypotheses beyond the definitions)
- `process_disagreement` (Full.lean, bits, any n), `process_disagreement_alphabet` (Gaps.lean, `Fin a`), `exclusivity` (Lift.lean, any alphabet). If w is a process function (unique fixed point for every local intervention) and s ≠ s', then some party k has s k ≠ s' k and w s k = w s' k.
- `extend_left_inv`, `extend_right_inv` (Full.lean, StinespringBoundary.lean). The source/sink map (o,e) ↦ (w o ⊕ e, o) is a bijection for every w.
- Cancel.lean: finite `native_decide` checks for Lugano, the identity loop and the cycle.
- `closed_not_every_w`: the identity loop has Gram diagonal 8 at the zero source.

### Proved only under assumptions (NOT the paper's theorem)
- Lift.lean `off_diagonal_cancels`, `diagonal_is_one`, and GramGeneral.lean `gram_unitary`. These are integer-valued (`Int`) "rows". Row orthonormality is a hypothesis, and in `gram_unitary` the witness party is also a hypothesis rather than being derived from the lemma. ComplexGram.lean contains only algebraic helper lemmas for a hand-rolled complex type.

## Not formalised
- Stinespring dilation and process-matrix validity (paper Section 2).
- Spacetime embedding (Gaps.lean defines `SpacetimeEmbeddingClaim : Prop := False` as a marker).

Build: `lake exe cache get && lake build` (fetches the Mathlib cache).
