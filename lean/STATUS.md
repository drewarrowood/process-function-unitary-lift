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
- Bookkeeping (PFUL/Bookkeeping.lean):
  - `PFUL.Choi.liftVecAnc`, `bornAnc`, `bornAnc_eq_bornC`, `bornAnc_eq_one`: AFNB normalisation with party ancillas, **group-free** (ancilla types need only Fintype + DecidableEq). Ancilla wires are identity wiring; internally a group structure is borrowed from `Fintype.equivFin` when needed, and the formula does not depend on it.
  - `PFUL.Choi.splitEquiv`, `bornSplit`, `bornSplit_eq_one`, `indSplit`, `bornSplit_eq_trace`, `afnb_iff_density_split`: the same in `ValidWith`'s split layout ((∀ k, I k) × (∀ k, X k)), plus the split-layout equivalence of AFNB normalisation with the density-matrix condition, for any map w and any local Kraus channels with ancillas.
  - `PFUL.Choi.validity_package`: one theorem bundling `ValidWith` (local unitaries), `valid_kraus` (local Kraus channels) and split-layout AFNB normalisation for all CP (`isCP_iff_choi`) and TP local Choi matrices.
- Infinite dimensions (TraceClass.lean, TraceValidity.lean; built against the pinned Mathlib, which has no trace-class theory). Hilbert-Schmidt: `hsSq_indep`, `hsSq_eq_adjoint`, `IsHS.comp_left/right`, `IsHS.adjoint`. Trace class = span of A†B with A, B Hilbert-Schmidt (`traceClass`): `hasSum_trace` (summable, basis-independent), `traceL` (linear), `trace_comp_comm` (Tr(CT) = Tr(TC)), `comp_mem_left/right`, `adjoint_mem` (ideal, *-closed), `trace_nonneg`, `rankOne_mem`, `trace_rankOne`, `trace_conj` (isometric conjugation), `traceNorm` = sup_{‖C‖≤1} |Tr(CT)| with `enorm_trace_le_traceNorm`, `traceNorm_ne_top`, `traceNorm_add_le`, `eq_of_trace_comp`. Tensor H ⊗ ℓ²(J) as ℓ²(J; H) (`tensor`, `slot`, `amp` = C ⊗ 1, `prodBasis`, `inner_tensor`), ℓ²(I×J) ≅ ℓ²(J; ℓ²(I)) (`l2ProdEquiv`). Partial trace `ptrace`/`ptraceR`: `trace_ptrace_comp` (Tr(Tr_J(T) C) = Tr(T (C⊗1))), `ptrace_unique`, `ptrace_add`, `ptrace_smul`, `ptrace_isPositive`, `trace_ptrace`, `hasSum_inner_ptrace`, `ptrace_rankOne_tensor`, `trace_ptraceR_comp`, `IsDensity.ptraceR`. Application: `PFUL.Countable.valid_density_l2` (every density operator on ℓ²(sources × input ancillas) goes to a density operator, and so does the sink state after tracing out the output ancillas). Literal Choi form and trace norm: see the two sections below.

## Literal Born pairing for countable alphabets: PFUL/BornPairing.lean
- Formulation: for infinite alphabets W = |U⟩⟩⟨⟨U| and the local Choi operators are not trace class, so Tr[W(...)] cannot be a trace of trace-class products. W is kept as the family of its row vectors `rowVec U r = U† e_r` (entries `conj (M r c)`, `rowVec_apply`). The pairing with ρ is the series `∑_r bornTerm U ρ r`, `bornTerm U ρ r = ⟪u_r, ρ u_r⟫`, over sink outcomes r = (o, y) (i.e. 1 on output ancillas). `HasSum` = convergence of the net of finite truncations. In finite dimensions this is exactly `PFUL.Choi.born_eq_trace`.
- `hasSum_bornTerm`: for any bounded U and trace-class ρ, the series converges to Tr(UρU†). `bornTerm_nonneg`: terms ≥ 0 for positive ρ.
- `PFUL.Countable.valid_born_l2`: same hypotheses as `valid_density_l2`; row entries are `conj ∏ₖ Vₖ(…)`, and for every density ρ the pairing has nonnegative terms, `HasSum … 1`, and equals `Tr[Tr_Y(ΦρΦ†)]`.
- Scope: here the local kernels are unitary; general channels are in PFUL/KrausL2.lean (next section).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Polar decomposition and ‖T‖₁ = Tr|T|: PFUL/Polar.lean
- `absOp T = CFC.abs T = √(T†T)`; `absOp_isPositive`, `absOp_mul_self` (|T|² = T†T), `norm_absOp_apply` (‖|T|x‖ = ‖Tx‖).
- `initSp T` = closure of range |T|; `isoPart` (isometry initSp → H, via `LinearMap.extendOfIsometry`); `partialIso T = isoPart ∘ P`.
- `polar`: T = V|T| for **every bounded T** (no compactness needed). `partialIso_of_mem_orthogonal` (V = 0 on initSpᗮ), `norm_partialIso_of_mem`, `norm_partialIso_le`, `adjoint_partialIso_comp` (V†V = P), `adjoint_partialIso_comp_self` (V†T = |T|).
- `absOp_mem`: T trace class ⇒ |T| trace class. `trace_absOp_eq`: Tr|T| is a nonnegative real equal to ‖√|T|‖₂². `traceNorm_eq_trace_abs`: **‖T‖₁ (= sup_{‖C‖≤1}|Tr CT|) = Tr|T|** for trace-class T.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `mem_traceClass_iff`: **T ∈ traceClass ↔ ∑ᵢ ⟪eᵢ, |T| eᵢ⟫ summable** (in any given Hilbert basis). Proof of ⇐: √|T| is Hilbert-Schmidt and T = (√|T| V†)† √|T|.
- `IsPartialIsometry V` (V V† V = V), `isPartialIsometry_partialIso`, `IsPartialIsometry.proj` (V†V idempotent and self-adjoint).
- `polar_unique`: if T = W A with A positive, ‖W(Ax)‖ = ‖Ax‖ and W = 0 on (range A)ᗮ, then A = |T| and W = partialIso T.
- Not done: compactness/spectral (Schmidt) decomposition of trace-class operators.

## General local channels on countable alphabets: PFUL/KrausL2.lean
- Encoding: a local channel ρ ↦ ∑_y K_y ρ K_y† with countably many Kraus operators K_y : ℓ²(I_k × X_k) → ℓ²(O_k) is its Stinespring kernel `V k (o, y) (i, x) = ⟨o|K_y|i,x⟩` (Kraus index y = output ancilla, Y k countable). Completeness ∑_y K_y†K_y = 1 ⟺ `hiso`: `HasSum (fun r => star (V k r c) * V k r c') (if c = c' then 1 else 0)` (orthonormal columns; rows need not be orthonormal). No countability needed on I k, X k.
- `induced_gram`: the induced kernel M r c = ∏ₖ Vₖ(rₖ)(w r k + c k, …) has orthonormal columns. Proof by polarization: for each pair of columns, a four-column polarized kernel per party (`(u + iᶠ v)/√2`) has unit columns, `induced_colnorm` gives unit norm of every polarized induced column, and `conj u · v = ½ ∑_φ conj(iᶠ)|(u + iᶠ v)/√2|²` (`polar_id`) is expanded multilinearly over the parties (`Fintype.prod_sum`).
- `induced_isometry_l2`: a linear isometry Φ : ℓ²(sources × X) →ₗᵢ ℓ²(sinks × Y) with Φ δ_c = M(·, c) (via `Orthonormal.orthogonalFamily.linearIsometry`).
- `valid_kraus_l2`: for every density ρ: ΦρΦ† and Tr_Y(ΦρΦ†) are density operators; the Born pairing (`bornTerm`, row vectors with entries conj ∏ₖ Vₖ) has nonnegative terms, `HasSum … 1`, and equals Tr[Tr_Y(ΦρΦ†)].
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Universes
- TraceClass.lean, Polar.lean, BornPairing.lean are universe-polymorphic: `H : Type u`; HS maps out of H may land in any universe (`K : Type v`); trace-class generators A†B factor through Hilbert spaces in H's universe (`gens`), and basis-independence statements quantify over index types `ι : Type u` (Hilbert bases of H exist with index in Type u). `rankOne_mem` was reproved without passing through ℂ (factor through H with a unit vector), which is what made the generalization possible.
- Countable.lean, Rows.lean, Assemble.lean, TraceValidity.lean, KrausL2.lean remain stated for alphabets in `Type` (finite parties `ι : Type`); these are combinatorial and were not generalised.

## Standalone Mathlib-style file: MathlibPR/PolarDecomposition.lean (lean_lib `MathlibPR`)
- Imports only Mathlib; namespace `ContinuousLinearMap`; `E : Type*`. `CFC.abs` based: `norm_abs_apply`, `polarInitial`, `polarIsometry`, `polarIsometry_comp_abs` (T = V|T|), `adjoint_polarIsometry_comp_polarIsometry_apply` (V†V = projection), `adjoint_polarIsometry_comp_self`, `norm_polarIsometry_le`, `IsPartialIsometry`, `isPartialIsometry_polarIsometry`, `polar_unique`. Builds; standard axioms only.


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
- Literal Choi form Tr[W(...)] = 1 in infinite dimensions (W is not trace class; the trace-form validity `valid_density_l2` is proved).
- Spacetime embedding (Gaps.lean defines `SpacetimeEmbeddingClaim : Prop := False` as a marker).

Build: `lake exe cache get && lake build` (fetches the Mathlib cache).

## Round 3

Proved (no `sorry`, axioms propext/Classical.choice/Quot.sound):
- `PFUL/Schmidt.lean`: `IsHS.isCompactOperator`, `isCompactOperator_of_mem` (trace class ⇒ compact);
  `PFUL.Polar.schmidt`: Hilbert basis v of eigenvectors of |T|, s ≥ 0, u orthonormal on {s ≠ 0},
  `HasSum (fun n => (s n * ⟪v n, x⟫) • u n) (T x)` (strong convergence), `HasSum s (trace |T|)`,
  ‖T‖₁ = Tr|T|.
- `PFUL/ChoiL2.lean`: Choi kernel of a Kraus kernel: `hasSum_choiKernel`, `choiKernel_tp`
  (Σ_o J(o,a;o,a') = δ), `choiKernel_psd` (finite sections PSD). Same `hiso` hypothesis as
  `valid_kraus_l2`, so every Kraus-specified channel's Choi kernel is covered.
- Universes: `TraceValidity`, `KrausL2`, `BornPairing` now universe-polymorphic (`ι : Type v`,
  alphabets `ι → Type u`); all other files already used `Type*`.
- `MathlibPR/PolarDecomposition.lean`: generalised to T : E →L[ℂ] F, `@[simp]` lemmas,
  `ker_polarAbs`, `ker_polarIsometry` (ker V = ker T), `polarInitial_orthogonal`, `polar_unique`.

Gaps:
- Converse Choi theorem in infinite dimensions (PSD + TP Choi kernel ⇒ countable Kraus
  factorisation). Needs a Kolmogorov/RKHS factorisation of a PSD kernel on a countable set plus a
  countable orthonormal basis of the closed span (Gram–Schmidt on an enumeration); the Choi
  kernel is not a bounded operator in general (identity channel), so square roots are unavailable.
- CP of Φ as a map on trace class is used only through `valid_kraus_l2` (entangled ancilla
  inputs); no standalone `IsCompletelyPositive` predicate on trace class is defined.
- Schmidt convergence is strong, not in trace norm.

Continuous alphabets (not formalised; scope):
- With counting measure, L²(X) = ℓ²(X) — exactly the countable case already covered.
- For a general measure, the permutation lift |o,e⟩ ↦ |w(o)+e, o⟩ is unitary on L² only if the
  shift e ↦ w(o)+e is measure-preserving (Haar measure on a locally compact group) and
  (o,e) ↦ (w(o)+e, o) is measurable; w must be a measurable process function.
- Unit columns used "expected number of fixed points = 1" via Tonelli over counting measure; the
  measure-theoretic analogue needs a Jacobian/change-of-variables condition for the fixed-point map
  and fails without it (fixed points of a continuous map have measure zero, so delta-normalised
  "states" are not in L²). One needs rigged Hilbert spaces or a direct-integral formulation.
- Required Lean infrastructure: Haar-measure L² unitaries for translations (Mathlib has
  measure-preserving maps and Lp, but not the translation unitary as `→L[ℂ]` on `Lp`), and
  direct integrals of Hilbert spaces (absent).

## Round 4

Proved (no `sorry`, axioms propext/Classical.choice/Quot.sound):
- `PFUL/ChoiConverse.lean`: `KernelPSD` (all finite sections PSD, complex order), `KernelPSD.herm`
  (PSD ⇒ Hermitian), `KernelPSD.exists_factor` (Kolmogorov factorisation over a countable index,
  via Mathlib's `RKHS.OfKernel` + Gram–Schmidt over an enumeration + `HilbertBasis.mk`), and
  **`exists_kraus_of_choi`**: a PSD, trace-preserving Choi kernel on countable `O × A` is
  `choiKernel V` for a Kraus kernel `V` over a countable `Y` satisfying `hiso` (the hypothesis of
  `valid_kraus_l2`).
- `PFUL/CPTP.lean`: `ampMap` (Φ ⊗ id_Z, finite Z), `IsCPTP` (trace class preserved, linear, TP,
  CP), `sandwich_mem`, `IsCPTP.isPositive`, `IsCPTP.isDensity`, `stinespring V`
  (ρ ↦ Tr_J(VρV†)) and **`isCPTP_stinespring`** (Kraus/Stinespring ⇒ CPTP, any Kraus index J).
- `PFUL/SchmidtTraceNorm.lean`: `traceNorm_sub_schmidt_le` (‖T − T_F‖₁ ≤ Σ_{n∉F} s_n),
  `tendsto_traceNorm_schmidt`, `PFUL.Polar.schmidt_traceNorm`.

Gaps:
- CPTP ⇒ Kraus (Stinespring dilation for normal CP maps on the trace class) is not formalised.
  Route: from Φ build the PSD Choi kernel J(o,a;o',a') = ⟨o|Φ(|a⟩⟨a'|)|o'⟩ (PSD by CP on finite
  ancillas), then `exists_kraus_of_choi`, then show the Kraus channel agrees with Φ on rank-ones
  and extend by trace-norm continuity — needs normality/trace-norm continuity of Φ (not part of
  `IsCPTP` as stated) and density of finite-rank operators in trace norm.
- `stinespring` is on abstract `H →L ℓ²(J;K)`; the bridge to the kernel form `V : O × Y → A → ℂ`
  used in `valid_kraus_l2` (building the isometry from the kernel) is not stated as a lemma.
- `ampMap` uses finite ancillas (n-positivity for all n, the standard CP definition).

## Round 5

Proved (no `sorry`, axioms propext/Classical.choice/Quot.sound):
- `PFUL/TraceNormDense.lean`: `exists_finiteRank_traceNorm_lt` (finite-rank operators are
  trace-norm dense in the trace class); `traceNorm_rankOne_le`, `enorm_inner_apply_le`,
  `norm_amp_le`, `traceNorm_ptrace_le`, `trace_conj_comp` (cross-space cyclicity),
  `traceNorm_conj_le`; `IsNormalCPTP` (IsCPTP + trace-norm bound ∃ c, ‖Φ T‖₁ ≤ c ‖T‖₁);
  `isNormalCPTP_stinespring`; `eq_of_rankOne_basis` (normal CPTP maps agreeing on matrix units
  agree on the trace class).
- `PFUL/KrausNormal.lean`: `krausIso`, `krausChannel` (ρ ↦ Tr_Y(UρU†), the `valid_kraus_l2`
  form), `krausStine`, **`krausChannel_eq_stinespring`** (bridge kernel form ↔ abstract
  Stinespring isometry), `isNormalCPTP_krausChannel`, `inner_krausChannel` (its Choi kernel is
  `choiKernel V`), `choiOf` with `choiOf_psd` (from CP) and `choiOf_tp`,
  **`exists_kraus_of_normalCPTP`**, **`isNormalCPTP_iff_kraus`** (Kraus ⟺ normal CPTP on
  countable ℓ²), `IsNormalCPTP.congr`, **`valid_normalCPTP_l2`** (validity for arbitrary normal
  CPTP local channels on countable alphabets).
- `PFUL/CommutingBlend.lean` (H.8.4 core, finite dimensions): `inner_eq_zero_or_norm_eq_one`
  (commuting rank-one projectors: parallel or orthogonal), `commuting_blend`
  (p_φ(i|o) = Σ_j |⟨b_j,φ⟩|² [f_j(o) = i], Σ_j |⟨b_j,φ⟩|² = ‖φ‖²).
- All deprecation warnings in PFUL removed (`if_pos/if_neg/dif_pos/if_true/if_false`,
  `coe_comp'`, `Set.mem_setOf_eq`, `Set.Infinite.diff`, `ofReal_norm_eq_enorm`, the
  `Mathlib.Data.Complex.Basic` import).

Gaps:
- Normality is defined as trace-norm boundedness; for maps linear on the trace class this is
  trace-norm continuity. (Automatic boundedness of positive TP maps is not proved.)
- H.8.4: that each deterministic record f_j is a process function (validity of 0/1 records,
  Appendix A) and the reduction "pairwise commuting P_{o,i} ⇒ hypothesis with b = u o₀" are
  not packaged; the H.8.1 Pauli-span equivalence is not formalised.
- Continuous alphabets: unchanged (not formalised).

## Round 6 (H.12 counterexample)

Proved (no `sorry`, no `native_decide`; finite computations by `decide +kernel`; axioms of
`purification_conjecture_false` and all key lemmas: propext/Classical.choice/Quot.sound):
- `PFUL/CounterexampleData.lean`: Gaussian-integer board tables (`U8 = tab`), board Gram
  check, 25 kernel-checked purity blocks (`purityBlock_all`, `TD_eq`), validity under the 64
  deterministic interventions (`valid_det`), the PF inequality check over 4 interventions
  (`pfCheck_eq`, `two_cases`), `g_pN = 32`, `g_pM = -24`.
- `PFUL/Counterexample.lean`: `board_mem_unitaryGroup` (each U_o unitary, U_o = H·diag(i^m)·H);
  general link product `compose` with ancillas `a : Fin 3 → Type`, `IsPure`;
  **`isPure_Vsb`** (Switchboard pure for all finite ancillas and local unitaries, via
  `scalar_key` multilinear reduction); `pcl_eq` (p = (pN + pM√2)/128); **`valid_pcl`**
  (all stochastic local interventions, via `stoch_decomp`); `Lg_nonneg_of_isPF`,
  `Lg_pcl_neg` (L(p) = (32 − 24√2)/128 < 0), `pcl_not_mem_convexHull`; `purifiable_pcl`;
  **`purification_conjecture_false`**: ∃ p, Valid p ∧ Purifiable p ∧ p ∉ convexHull ℝ PFset.
- Build: CounterexampleData ≈130 s (≈2.6 GB peak), Counterexample a few seconds.

Gaps:
- Ancillas: finite types in `Type 0` only (infinite-dimensional ancillas not covered).
- Purity/validity/PF are this file's finite-dimensional definitions (link-product `compose`,
  `Valid` over product stochastic interventions, `IsPF` as unique fixed point); they are not
  yet linked to the `PFUL.Validity`/`Choi` framework.


## Round 7

Proved (no `sorry`, no `native_decide`; axioms propext/Classical.choice/Quot.sound, `tau_bijective` only propext/Quot.sound):
- `PFUL/CounterexampleLink.lean`: `bitsEquiv` (Fin 8 ≃ 3-bit strings), **`isPF_iff`** (`IsPF w` ↔
  `PFUL.Countable.IsProcessFunction (wBits w)`), `isPF_iff_column`, **`valid_pfPoint`** (via
  `PFUL.Column.sum_prod_eq_one`), **`valid_of_mem_convexHull`**, `purification_conjecture_false'`
  (H.12 restated with the general process-function definition).
- `PFUL/Continuous.lean` (F.5 core; groups of any cardinality, no measure): `tau` (o ↦ o − w o),
  **`tau_bijective`**, **`fiber_const`** (w_a constant where τ agrees off a), `tauInv_apply`
  (τ⁻¹(e)_a = e_a + c_a e), **`c_indep`** (c_a independent of e_a).

Gaps:
- F.5.3 (τ measure-preserving for Haar measure; induction on parties + Tonelli + Lusin–Souslin) and
  F.5.5 (unitarity for point-map local unitaries) are paper proofs only.
- Counterexample: `IsPure` (link-product purity) is not identified with the W = |U⟩⟩⟨⟨U| form of
  `PFUL.Choi`; ancillas finite in `Type 0`.
- Normality assumed in `IsNormalCPTP` (automatic boundedness of positive TP maps not proved).


## Round 8

Proved (no `sorry`, no `native_decide`; axioms propext/Classical.choice/Quot.sound):
- `PFUL/ContinuousMeasure.lean` (F.5.3): `tau_measurable`, **`tauInv_measurable`** (Borel inverse via
  `Measurable.measurableEmbedding`, Lusin–Souslin), **`tau_measurePreserving`**: for `ι` finite and each
  `G k` an additive commutative group with `MeasurableAdd`, `MeasurableSub₂` and `StandardBorelSpace`, and
  `μ k` σ-finite and right-invariant, `MeasurePreserving (tau w) (Measure.pi μ) (Measure.pi μ)` for every
  measurable process function `w` (causal or not). Proof by induction on `card ι`
  (`piEquivPiSubtypeProd`, `MeasurePreserving.skew_product`, shear via `measurePreserving_sub_right`,
  `fiber_const`). Corollaries: `tau_measurePreserving_real` (ℝ, Lebesgue), `tau_measurePreserving_circle`
  (`AddCircle T`, Haar). Countable groups with counting measure are covered by the general theorem.
- `PFUL/ContinuousUnitary.lean` (F.5.5, translation class): `phaseUnitary` (multiplication by a measurable
  unit-modulus phase, unitary on L²), `koopman` (Koopman unitary of a measure-preserving measurable
  equivalence), `tauEquiv`, **`closedLoop_unitary`**: ∃ U : L² ≃ₗᵢ[ℂ] L² with
  (Uψ)(o) = φ(o)ψ(o − w o) a.e.
- `PFUL/ChoiLink.lean`: `choiVec`, `choiMat` (= |V⟩⟩⟨⟨V|), `choiVec_apply`, **`compose_eq_link`**,
  **`compose_congr_choiVec`** (purity depends only on |V⟩⟩), `choiMat_isHermitian`, `choiMat_sq`
  (W² = (Tr W)W), **`Vsb_pure_choi`**.

Gaps (with reasons):
- F.5.5 for general point maps g (|u|² = Jacobian): this needs the change of variables formula for
  measurable bijections with a Jacobian (Mathlib has it for injective differentiable maps on ℝⁿ,
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul`). The paper reduces it to the translation case.
  Not done this round.
- Infinite-dimensional ancillas: `compose`/`IsPure` are matrix-level (finite `Fintype` ancillas). An
  infinite-ancilla purity notion needs bounded operators on ℓ²(a) ⊗ ℂ^{…}. Finite ancillas do **not**
  logically suffice, because infinite-ancilla purity is a stronger hypothesis. The paper argument
  (the proof of `isPure_Vsb` is uniform in the ancilla) is not formalised.
- `Valid` (counterexample) vs `PFUL.Validity.ValidWith`: still checked on paper only.
- Automatic boundedness/normality of positive TP maps (dropping the assumption in `IsNormalCPTP`):
  not attempted. This is a genuine theorem in the infinite-dimensional case (CP + TP on trace class
  ⇒ bounded is true; normality is not automatic for maps on B(H)), and Mathlib lacks the needed
  order-theoretic operator machinery.


## Round 9: operator machinery for countable ancillas (`PFUL/CounterexampleInf.lean`)

All sorry-free; axioms are only propext, Classical.choice and Quot.sound; no native_decide.
- `entOp A` gives the kernel ⟨e_r, A e_c⟩ of a bounded operator on ℓ²(X) = `lp (fun _ => ℂ) 2`.
  `isIsoKernel_entOp`: a unitary has orthonormal columns (stated with HasSum).
- `exists_isometry_of_isIsoKernel`: if a kernel's columns are orthonormal, it is the kernel of a
  linear isometry of ℓ².
- `composeOp V A`: the bounded-operator compose for countable ancillas κ_k. It is defined as
  `compose V (entOp ∘ A)`; the ancilla sums are absolutely convergent series. Summation helpers:
  `hasSum_pi_prod` and `hasSum_prod_fintype`.
- `IsPureKer` / `IsPureInf`: purity against every family of countable ancillas.
  `IsPureKer.isPureInf` turns the kernel form into an ℓ² isometry. `IsPureKer.isPure` gives
  agreement with the matrix `IsPure` on finite ancillas.
- `isPureKer_Vsb` and `isPureInf_Vsb`: the Switchboard is pure against countable ancillas.
- `purification_conjecture_false_inf`: `pcl` is Valid, is `PurifiableInf`, and lies outside the
  process-function hull.

Gaps:
- Unitarity, not only isometry, for infinite ancillas. Proving surjectivity needs orthonormal rows,
  which the scalar-key argument does not provide. Ancillas of uncountable dimension are not covered.
- Goal 4 is not done this round, for two reasons. The link between `Valid` and
  `PFUL.Validity.ValidWith` needs a bridge between the counterexample's `Fin 8` encoding and the
  general typeclass setup; this is checked on paper only. F.5.5 for general point maps needs change
  of variables for measurable bijections with a Jacobian, which is not formalised.

## Round 10 (Oct 23 2026)

New files: `CounterexampleRows.lean`, `CounterexampleUnitary.lean`, `CounterexampleValidity.lean`, `ContinuousJacobian.lean`. All are sorry-free, use no `native_decide`, and depend only on the axioms propext, Classical.choice and Quot.sound.
- `row_scalar_key` (CounterexampleRows): the row orthonormality identity for the Switchboard. It is checked in the kernel by `decide +kernel` over 16 blocks.
- `isCoIsoKernel_compose_Vsb` and `surjective_of_isCoIsoKernel`: an isometry whose kernel has orthonormal rows is onto ℓ².
- `isUnitaryInf_Vsb` and `purification_conjecture_false_unitaryInf`: the Switchboard loop is **unitary**, not only isometric, against every family of countable ancillas. `pcl` is Valid, is purifiable by a unitary in that sense, and lies outside the PF hull.
- `valid_pfPoint_iff` and `validWith_of_valid_pfPoint`: for a deterministic w, `Valid (pfPoint w)` holds iff `IsPF w`, and either implies `PFUL.ValidWith (wBits w) X Y` for all finite X and Y.
- `PFUL.Continuous.closedLoop_general_unitary`: for a measurable bijection g that carries ρ·μ to μ, with ρ measurable and ρ > 0, and a measurable unimodular phase φ, the map ψ ↦ φ·√ρ·(ψ∘g) is a unitary on L²(μ). This is F.5.5 for general point maps.
- `PFUL.Continuous.closedLoop_jacobian_unitary`: the same statement for a global C¹-type bijection of a finite-dimensional real space, with derivative g', det g' ≠ 0, measurable |det g'|, and μ an additive Haar measure. Here ρ = |det g'|, obtained from Mathlib's change of variables.

Gaps:
- `ValidWith` is defined only for deterministic processes. For the non-deterministic `pcl`, the validity link is a category mismatch, not a missing proof.
- The F.5.5 result needs ρ > 0 everywhere and a global bijection. It does not cover local diffeomorphisms or a degenerate Jacobian.
- Ancillas of uncountable dimension are still not covered.
- Math goals 4 (non-X 3-term boards) and 5 (the 23 never-crossed inequalities) were not attempted this round.

## Round 11 (Oct 23 2026)

New files: `CounterexampleAuto.lean`, `LiftAuto.lean`, `ContinuousLocal.lean`. All sorry-free, no `native_decide`, axioms only propext, Classical.choice and Quot.sound (checked with `#print axioms`).
- **Automatic boundedness.** `PFUL.Counterexample.unitary_of_unitaryKernel`: a kernel with orthonormal columns and rows, over an index set of any cardinality, is the matrix of a bounded unitary of ℓ². No operator or boundedness hypothesis.
- `IsUnitaryKer` / `isUnitaryKer_Vsb`: the Switchboard loop is unitary for local operations given only as unitary kernels, with ancillas of **any cardinality**. `IsUnitaryAll` / `isUnitaryAll_Vsb`: Round 10's `IsUnitaryInf` without the `Countable` hypothesis (it was never used). `purification_conjecture_false_unitaryKer`: strongest form of H.12.1.
- `PFUL.LiftAuto.permPhaseUnitary`, `closedLoop_l2_unitary`: for any index set and any bijection, ψ ↦ φ·(ψ∘e) is a unitary of ℓ²; for every process function on groups of any cardinality, ψ ↦ φ(o)ψ(o − w o) is a unitary of ℓ²(∏ G_k), with no measurability, countability or boundedness assumed.
- `PFUL.Continuous.densityIsoₗᵢ`: √ρ-multiplication is an isometry L²(ρμ) → L²(μ) for every measurable ρ ≥ 0.
- `closedLoop_isometry`: any measurable g (not necessarily injective) with g_*(ρμ) = μ gives an isometry ψ ↦ φ√ρ(ψ∘g). `closedLoop_unitary_ae`: unitary if g is a measurable bijection and ρ ≠ 0 a.e.
- `closedLoop_jacobian_isometry`: g measurable, injective and differentiable (within s) on a conull measurable s with conull image; Jacobian may vanish; weight √|det g'|; isometry. `closedLoop_jacobian_unitary_ae`: measurable bijection, differentiable off a null set, conull image of s, det g' ≠ 0 a.e.: unitary. Covers piecewise-smooth bijections (e.g. threshold Lugano lifts).

Gaps:
- Hypotheses kept: measurability of |det g'| and the conull image of s (Lusin (N)); the latter is necessary (singular homeomorphisms). Non-injective local diffeomorphisms are not isometries (degree factor), so they are outside the point-map class.
- The composite F.5.5 statement (point map g composed with τ_w in one formula) is not restated in Lean; it is a composition of `closedLoop_unitary` with `closedLoop_jacobian_unitary_ae`.
- Conjecture F.5.7: Proposition F.5.8 (causal w, strong convergence of discretisations to the circuit loop) is proved on paper only; for Fourier-type V_k it is conditional on fixing strongly convergent unitary grid approximants. The non-causal case is OPEN.
- Automatic boundedness/normality of positive TP maps on trace class (Round 8 gap) is unchanged.

## Lemma H and the class bound, H.17.17 (Oct 24 2026)

New file: `PFUL/LemmaH.lean` (Mathlib only, standalone). No sorry, no `native_decide`, no new axioms. `#print axioms` gives only propext, Classical.choice and Quot.sound for every main theorem (`LemmaH_axioms.log`). Build: `lake build PFUL.LemmaH`.

**Model.**
- A three-qubit Pauli string modulo phase is `PStr = Fin 3 → ZMod 2 × ZMod 2`, with (x, z) bits per site.
- An operator is given by its Pauli expansion `PStr →₀ ℂ`. The product of expansions is the twisted convolution `tmul φ`, with σ_t σ_s = φ t s σ_(t+s).
- The theorems only need `φ t s ≠ 0`, so they cover the Pauli phases ±1, ±i.
- Anticommutation is the symplectic form, and `Rigid p S` means the qubit-p parts are injective on S.

**Proved.**
- `rigid_two`, `rigid_three` (Lemma H(i)): {1, A} with A ≠ 1, and {1, A, B} with A, B anticommuting, each have a rigid qubit.
- `card_support_tmul`: if all strings of W share their π-part and π is injective on supp V, then |supp W·V| = |supp W|·|supp V|. This holds for any abelian groups G, H, any additive map π, and any nonvanishing φ.
- `lemmaH_ii` (Lemma H(ii)): suppose V_y = W·V_x, where all strings of W have the same qubit-p part, p is rigid for V_x, |supp V_x| ≥ 2, |supp V_y| ≤ 3 and V_y ≠ 0. Then W is a single string times a nonzero scalar.
- `RigidBoard`: the abstract cube with a labelling, an identity label, rigid directions, and closure along rigid directions.
  - `even_card_class`: every class, the identity included, has even size.
  - `card_class_ge_two`: every occurring class has size ≥ 2.
  - `card_image_le_four`: at most 4 classes.
  - `card_class_eq_two_of_four`: if k = 4, each class has 2 vertices.
  - `class_eq_edge_of_four`: if k = 4, a non-identity class is the edge {o, o + e_p}.
  - `rigid_unique_of_four`: if k = 4, a non-identity class has a unique rigid qubit.
- `classBound`: end to end, k ≤ 4, and k = 4 ⇒ every class has 2 vertices.

**Hypotheses of `classBound`, from the paper and not proved in Lean.**
- `hshape`: the support shapes of H.17.12.
- `hle3`: at most three terms.
- `hne`: class operators are nonzero.
- `hB`: the factorisation V_y = W·V_x with W p-constant across class-changing p-edges (Lemma B plus unitarity).
- `hcls`: labels are classes, i.e. operators equal up to a left Pauli and a nonzero scalar have equal labels.
- That `tmul` with the Pauli cocycle is the operator product is the standard Pauli multiplication table. It is not derived from matrices here.

## Round 12 (Oct 24 2026): the counterexample in the process-matrix (Choi) framework; infinite ancillas

New files: `ProcessMatrix.lean`, `CounterexampleChoi.lean`, `CounterexampleHilbert.lean`. All sorry-free, no `native_decide`, no new axioms; `#print axioms` gives only propext, Classical.choice and Quot.sound for every main theorem (`Round12_axioms.log`). Build: `lake build PFUL.ProcessMatrix PFUL.CounterexampleChoi PFUL.CounterexampleHilbert`.

**Framework (`PFUL.PM`, finite-dimensional: every type is a Fintype).**
- `IsCPTPChoi J`: J ⪰ 0 and Σ_b J((a,b),(a',b)) = δ_{aa'}. `isCPTPChoi_choiOf_iff`: equivalent to `PFUL.Choi.IsCP Φ` plus trace preservation for the map Φ with Choi matrix `choiOf Φ`.
- `link W C`: the CDP link product in indices, W on P × F × ∏(I_k × O_k), C_k on (I_k × X_k) × (O_k × Y_k).
- `IsValidPM W`: W ⪰ 0 and W ∗ C is CPTP (as a Choi matrix P × ∏X → F × ∏Y) for all finite ancillas and all CPTP C_k.
- `UnitaryLink W`, `IsPurePM W := IsValidPM W ∧ UnitaryLink W` (AFNB Def. 1, finite ancillas).
- Lemmas: `link_posSemidef`, `link_rankOne`, `isUnitaryM_of_vecOp_eq`.

**Bridges (`CounterexampleChoi.lean`).**
- `isValidPM_Wcl_iff : IsValidPM (Wcl p) ↔ Valid p` (diagonal process matrix of p).
- `isValidPM_Wcl_pfPoint_iff : IsValidPM (Wcl (pfPoint w)) ↔ PFUL.Countable.IsProcessFunction (wBits w)`.
- `isPure_iff_unitaryLink : IsPure V ↔ UnitaryLink (choiMat V)` (every V), via `link_choiMat_vecOp`.
- `trace_link_Vsb`, `isValidPM_choiMat_Vsb`, `isPurePM_choiMat_Vsb`: W = |Vsb⟩⟩⟨⟨Vsb| is valid and pure in the framework sense.
- `inducedP_eq_born`: the induced process is the Born rule of W.
- `purification_conjecture_false_choi`: H.12.1 with framework definitions only (valid process matrix, pure process matrix + normalised source, outside the hull of valid deterministic process matrices).

**Infinite ancillas (`CounterexampleHilbert.lean`).**
- `kerOf`, `isIsoKernel_kerOf`, `isCoIsoKernel_kerOf`: the matrix of a unitary in any Hilbert basis is a unitary kernel.
- `IsPureHilbert V`: unitary loop for ancillas in arbitrary Hilbert spaces (Hilbert bases indexed by Bool × κ_k). `isPureHilbert_iff_isUnitaryKer` (every V). `isPureHilbert_Vsb`.
- `compose2`, `isIsoKernel_compose2_Vsb`: different input/output ancillas, any cardinality, isometric kernels.
- `krausLoop`, `isIsoKernel_krausLoop`, `valid_normalCPTP_Vsb`: validity of the Switchboard under arbitrary normal CPTP local channels on countable ancillas.

Gaps:
- `IsValidPM`/`IsPurePM` are finite-dimensional definitions; infinite ancillas are covered by separate kernel, Hilbert-basis and Kraus statements, not by an infinite-dimensional link product of non-trace-class Choi operators.
- `IsPure V → IsUnitaryKer V` for general V (finite-ancilla purity implies infinite-ancilla purity) is proved on paper only (lift.md H.19.4). Not needed for Vsb.
- AFNB Thm 2 (pure ⟺ W is the Choi projector of a unitary) is not formalised.
- Normal CPTP validity needs countable ancilla alphabets (the Kraus theorem used is for countable ℓ²).
