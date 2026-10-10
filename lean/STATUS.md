# Lean status (Lean 4.34.1, Mathlib v4.34.1)

## Main result: PFUL/UnitaryLift.lean (uses Mathlib)
- `PFUL.IsProcessFunction w`: for every `f : ∀ k, I k → O k`, there is exactly one `s` with `f k (w s k) = s k` for all k.
- `PFUL.exclusivity`: the lemma, derived here and not assumed. For s ≠ s' there is a k with s k ≠ s' k and w s k = w s' k.
- `PFUL.induced`: M (s,y) (e,x) = ∏ k, V k (s k, y k) (w s k + e k, x k).
- `PFUL.induced_mul_conjTranspose`: if w is a process function and V k * (V k)ᴴ = 1 for every k, then M * Mᴴ = 1. This holds over any field with a star operation (`Field 𝕜`, `StarRing 𝕜`), for any finite set of parties `ι`, finite input groups `I k`, finite output sets `O k`, and finite local ancillas `X k`, `Y k`. Input and output sizes may differ.
- `PFUL.induced_mul_conjTranspose_complex`: the same theorem with 𝕜 = ℂ.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no custom axioms, no `native_decide`.
- `PFUL.card_eq`: the dimension count. If |I k × X k| = |O k × Y k| for every k, the source⊗ancilla and sink⊗ancilla index types have the same cardinality.
- `PFUL.induced_unitary` (ℂ): for any bijection `e` between those index types, `(induced ℂ w V).submatrix id e ∈ Matrix.unitaryGroup _ ℂ`.
- `PFUL.induced_conjTranspose_mul` (ℂ): `Mᴴ * M = 1`. Together with `induced_mul_conjTranspose`, M is unitary on both sides.
- All of the above depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Column side via logical consistency: PFUL/Column.lean (Appendix F.3)
- `PFUL.Column.sum_prod_eq_one`: for a process function w (finite parties, finite alphabets, no group structure needed) and any family q k i : O k → R over a commutative ring with ∑ o, q k i o = 1, `∑ s, ∏ k, q k (w s k) (s k) = 1`. Proof: average the number of fixed points over the product measure on deterministic interventions (the finite-alphabet form of the Tonelli argument).
- `PFUL.induced_colnorm` (ℂ): if (V k)ᴴ * V k = 1 for all k, every diagonal entry of Mᴴ M is 1 (unit columns).
- `PFUL.induced_conjTranspose_mul_of_colnorm` (ℂ): if V k are unitary (both V Vᴴ = 1 and Vᴴ V = 1), then Mᴴ M = 1. The proof uses orthonormal rows (`induced_mul_conjTranspose`) and unit columns, so 1 - Mᴴ M is a projection with zero diagonal, hence 0. **No dimension count** (no `card_eq`, no square-matrix argument). Input and output sizes may differ, as long as each local V k is unitary.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Not formalised: the countable (infinite-alphabet) version (tsum/Tonelli and l^2 operators). Appendix F.3's countable argument is on paper only.

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
