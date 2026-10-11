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

## Countable alphabets: PFUL/Countable.lean (Appendix F.3)
Finitely many parties (`Fintype ι`); input alphabets `I k` arbitrary (any cardinality); output alphabets `O k` and sink ancillas `Y k` countable; values in `ℝ≥0∞` with `tsum`.
- `PFUL.Countable.tsum_prod_eq_one`: if w is a process function and `∑' o, q k i o = 1` for all k, i, then `∑' s, ∏ k, q k (w s k) (s k) = 1`. Proof: product measure `Measure.infinitePi` of the PMFs on the space of all deterministic interventions `(Σ k, I k) → O`; the events "s is the fixed point" are disjoint cylinders covering the space.
- `PFUL.Countable.tsum_prod_eq_one_anc`: the same with each output paired with a sink-ancilla label (`q k i` a probability vector on `O k × Y k`).
- `PFUL.Countable.induced_colnorm`: for complex kernels `V k : O k × Y k → I k × X k → ℂ` with unit-norm columns (`∑' r, ‖V k r c‖₊² = 1`), every column of the induced map `∏ k, V k (f k, y k) (w f k + e k, x k)` has unit norm: `∑' (f,y), ‖M (f,y) (e,x)‖₊² = 1`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- `PFUL.Countable.hasSum_pi_prod` (PFUL/Rows.lean): factorisation lemma. For a finite index type K, countable X k and absolutely summable g k : X k → ℂ, `HasSum (fun x => ∏ k, g k (x k)) (∏ k, ∑' x, g k x)`. Proof: product of counting measures (`Measure.pi count = count`) and Fubini (`integral_fintype_prod_eq_prod`). The ℝ≥0∞ version was not needed and is not stated separately; the column identity was proved directly.
- `PFUL.Countable.exclusivity`: the exclusivity lemma for arbitrary alphabets.
- `PFUL.Countable.induced_rows`: orthonormal rows. If each V k has square-summable orthonormal rows, then for all sink indices r, r', `HasSum (fun c => M r c * conj (M r' c)) (if r = r' then 1 else 0)`, with the series convergent.
- `PFUL.Countable.orthogonal_span_eq_bot` (PFUL/Assemble.lean): an orthonormal family is total if Parseval holds on a separating family (proof by Bessel's inequality on the family extended by a unit vector orthogonal to it).
- `PFUL.Countable.induced_unitary_l2`: **the induced map is unitary on ℓ².** Hypotheses: finitely many parties; I k, X k, O k, Y k countable; each V k has square-summable orthonormal rows and unit-norm columns (a unitary kernel). Conclusion: there is a linear isometric *equivalence* `Φ : ℓ²(sources × ancillas) ≃ₗᵢ[ℂ] ℓ²(sinks × ancillas)` with `Φ v r = ∑' c, M r c * v c` (as a HasSum) and `Φ (single c 1) r = M r c`. So Φ is the induced operator, and it is unitary (isometric and surjective; M M† = 1 and M† M = 1).
- Axioms for all of the above: `propext`, `Classical.choice`, `Quot.sound`.
- Remaining limits: finitely many parties; continuous alphabets not covered.

## Appendix A, validity: PFUL/Validity.lean (finite dimensions)
- `PFUL.ptrace` (partial trace over the second tensor factor), `PFUL.ptrace_posSemidef`, `PFUL.trace_ptrace`.
- `PFUL.IsDensity ρ`: PSD and trace 1. `PFUL.density_of_isometry`: if Mᴴ M = 1 and σ is a density matrix, then M σ Mᴴ and its partial trace are density matrices.
- `PFUL.ValidWith w X Y` (the AFNB-style validity condition used in Appendix A): for all local unitaries V k : I k × X k → O k × Y k (Stinespring dilations) and all joint density matrices σ of source and input ancillas (entanglement and shared ancillas allowed), the global output and the sink state (partial trace over output ancillas) are density matrices.
- `PFUL.valid`: every process function satisfies `ValidWith w X Y` for all finite ancilla types X, Y.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Gaps closed (PFUL/Isometry.lean, PFUL/Channels.lean, PFUL/Choi.lean):
  - `PFUL.Column.sum_prod_eq_prod`: column identity with constant row sums λ_k (over ℂ): Σ_s ∏_k q_k(w s k)(s k) = ∏_k λ_k (proof: normalise, use the λ=1 case, polynomial identity in a perturbation parameter).
  - `PFUL.induced_isometry`: isometric (not necessarily square) local maps give Mᴴ M = 1.
  - `PFUL.krausDilP`, `PFUL.krausDilP_isometry`, `PFUL.ptrace_krausDil`: Stinespring dilation V = Σ_j K_j ⊗ |j⟩ of any Kraus family is an isometry and reproduces the channel Σ_j K_j ρ K_jᴴ.
  - `PFUL.valid_kraus`: validity (global output and sink state are density matrices) for arbitrary local CPTP maps in Kraus form, with arbitrary joint (entangled/shared) states of source and ancillas.
  - `PFUL.outcomeState`, `PFUL.outcomeState_posSemidef`, `PFUL.sum_outcomeState`, `PFUL.valid_instrument`: local instruments; every outcome-conditioned sink state is PSD, they sum to a density matrix, and outcome probabilities sum to 1.
  - `PFUL.Choi.procMat` (W = |U⟩⟩⟨⟨U|), `PFUL.Choi.choi`, `PFUL.Choi.born`/`bornC` (generalised Born rule Tr[W (ρ ⊗ 1_F ⊗ ⨂ C_k)ᵀ]), `PFUL.Choi.born_eq_trace` (Born rule = Tr[M ρ Mᴴ]), `PFUL.Choi.born_eq_one`, `PFUL.Choi.kraus_of_choi` (PSD Choi matrix ⇒ Kraus family, via the spectral theorem; TP ⇒ complete), `PFUL.Choi.bornC_eq_one`: AFNB/OCB normalisation Tr[W(...)] = 1 for every source state and all local CPTP Choi matrices.
- Edges closed (PFUL/ChoiAnc.lean, PFUL/ChoiThm.lean):
  - `PFUL.Choi.wAnc`, `wAnc_isProcessFunction`, `born_anc_eq_one`, `bornC_anc_eq_one`: Choi-form normalisation with party ancillas. Local maps I_k × X_k → O_k × Y_k; the source state ρ is a joint state of the source and all input ancillas, so shared or entangled ancillas are folded into it; the ancilla wires are identity channels from source to party and from party to sink. (Technical assumption: each X_k carries an AddCommGroup instance, as any finite set can, e.g. Fin n; the formula only uses 0 + x = x.)
  - `PFUL.Choi.procMat_posSemidef`: W = |U⟩⟩⟨⟨U| is PSD.
  - `PFUL.Choi.afnb_iff_density`: for any map w and fixed local Kraus channels, AFNB normalisation (Born rule = 1 for all density matrices ρ) ⇔ the induced output M ρ Mᴴ is a density matrix for all ρ. Positivity is automatic; the content is the trace. With `wAnc` this covers party ancillas.
  - `PFUL.Choi.ampliate`, `IsCP`, `choiOf`, `cp_choi_posSemidef`, `apply_eq_sum_choi`, `choi_posSemidef_cp`, `isCP_iff_choi`: **Choi's theorem.** A linear map Φ is CP (Φ ⊗ id_n preserves PSD for all n) iff its Choi matrix is PSD. CP is now a theorem, not a definition.
- Still not covered: the equivalence `afnb_iff_density` is stated in the Choi-file indexing (source ⊗ ancillas as one register, ∀ k, I k × X k), not literally for `ValidWith` with its (∀ k, I k) × (∀ k, X k) indexing (a reindexing). Infinite dimensions are not covered in the Choi form.


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
- Reindexing `afnb_iff_density` to the literal `ValidWith` index types; Choi form in infinite dimensions.
- Spacetime embedding (Gaps.lean defines `SpacetimeEmbeddingClaim : Prop := False` as a marker).

Build: `lake exe cache get && lake build` (fetches the Mathlib cache).
