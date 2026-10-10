# Lean status (Lean 4.34.1)

Build: `cd lean && lake build`. Every file compiles. There is no `sorry`, `admit` or `axiom` declaration. Files that use `native_decide` also depend on the compiler-trust axiom `Lean.ofReduceBool`: Full.lean (`hadamard_rows_orthogonal` only), Gaps.lean (`hadamard_rows`, `trace_identity_ancilla`), Cancel.lean (finite checks), and StinespringBoundary.lean (`closed_not_every_w`).

## Proved (no hypotheses beyond the definitions)
- `process_disagreement` (Full.lean, bits, any n), `process_disagreement_alphabet` (Gaps.lean, `Fin a`), `exclusivity` (Lift.lean, any alphabet). If w is a process function (unique fixed point for every local intervention) and s ≠ s', then some party k has s k ≠ s' k and w s k = w s' k.
- `extend_left_inv`, `extend_right_inv` (Full.lean, StinespringBoundary.lean). The source/sink map (o,e) ↦ (w o ⊕ e, o) is a bijection for every w.
- Cancel.lean: finite `native_decide` checks for Lugano, the identity loop and the cycle.
- `closed_not_every_w`: the identity loop has Gram diagonal 8 at the zero source.

## Proved only under assumptions (NOT the paper's theorem)
- Lift.lean `off_diagonal_cancels`, `diagonal_is_one`, and GramGeneral.lean `gram_unitary`. These are integer-valued (`Int`) "rows". Row orthonormality is a hypothesis, and in `gram_unitary` the witness party is also a hypothesis rather than being derived from the lemma. ComplexGram.lean contains only algebraic helper lemmas for a hand-rolled complex type.

## Not formalised
- The theorem M M† = 1 for complex local unitaries.
- Stinespring dilation and process-matrix validity (paper Section 2).
- Spacetime embedding (Gaps.lean defines `SpacetimeEmbeddingClaim : Prop := False` as a marker).
