# 2026-11-03 — Infinitely many parties: ZFC settles it (exclusive ⇏ PF)

**Question (addenda D–F of 2026-11-02-general-alphabets.md; lift.md Appendix M).** With infinitely
many parties, is every exclusive classical process (unique fixed point for every local
intervention, `Exclusive` in `lean/PFUL/InfiniteParties.lean`) a process function?
Known before: yes for continuous `w` (InfiniteCompact.lean); no under cov(M)=𝔠 / CH
(CovMCounterexample.lean).

**Answer: ZFC alone gives a counterexample — and it is explicit and Borel; no choice-heavy
diagonalisation is needed.** [proved-in-Lean: `lean/PFUL/ZFCCounterexample.lean`,
`PFUL.Infinite.exists_exclusive_not_pf`, axioms `propext, Classical.choice, Quot.sound` only;
no hypothesis.] Hence the cov(M)/CH hypotheses in CovMCounterexample.lean are superfluous
(that file remains correct, just subsumed).

## The map
Countably many binary parties, `s : ℕ → Bool`. By `exists_exclusive_not_pf_iff` it suffices to
find a fixed-point-free exclusive `F : 2^ℕ → 2^ℕ`. Let `E` = finitely supported sequences.
- `s ∉ E` (infinitely many 1s): `F s = 0`.
- `s ∈ E`: `F s = e₀ ⊕ (s shifted right)`, i.e. `F s 0 = 1`, `F s (k+1) = s k`.

**No fixed point** [proved-on-paper and in Lean]. If `s ∉ E` then `F s = 0 ∈ E ≠ s`. If `s ∈ E` and
`F s = s` then `s 0 = 1`, `s (k+1) = s k`, so `s` is all ones, not in `E`.

**Exclusive** (for `s ≠ s'` find `k` with `s k ≠ s' k` and `F s k = F s' k`):
- both ∉ E: `F s = F s' = 0`; any differing coordinate works.
- both ∈ E: let `m` = least coordinate where they differ. If `m = 0`, both values are 1;
  otherwise `F s m = s (m−1) = s' (m−1) = F s' m` by minimality.
- `s ∉ E`, `s' ∈ E` with support below `N`: pick `k ≥ N+1` with `s k = 1`; then `s' k = 0` and
  `F s' k = s' (k−1) = 0 = F s k`.

## Why this gives a non-PF and the key idea
Each party `k` in the fixed-point equation with identity interventions copies `F s k` to `s k`;
there is no consistent assignment, yet exclusivity holds, so for every intervention there is
*at most* one fixed point (fixed_unique) but for the identity there is none.
Idea: in XOR form `G(s) = F s ⊕ s`, exclusivity says `(s⊕s') ∧ (Gs⊕Gs') ≠ 0` and
fixed-point-freeness says `G s ≠ 0`. `G = id` works except at `0`; the "Hilbert hotel" repair
uses the linear map `L d = d ⊕ shiftRight d` (which satisfies `d ∧ L d ∋ min supp d`) on the
countable subspace `E`, where `L(E)` = even-weight vectors, so translating by `e₀` avoids 0; the
mismatch between `E` and its complement is harmless because both images differ from `s` only
finitely on the infinite set `supp s`. Compactness (the continuous theorem) is what fails: `F` is
discontinuous (it is Borel, class ≤ 2, since `E` is F_σ).

## Literature (search done 2026-11-02 evening; fetched sources only)

**Verdict: apparently new, with a close finite analogue.** I found no source that studies process
functions/exclusivity with infinitely many parties, and none containing this map or an equivalent
infinite-dimensional counterexample. The closest literature is the finite Boolean-network theory
of the *conjugate* `x ⊕ f(x)`, which is exactly our `G`.

1. **Process functions, finite parties only** [cited]. Baumeler–Wolf define process functions for
   N parties by the unique-fixed-point condition. Baumeler, Costa, Ralph, Wolf, Araújo,
   "Reversible time travel with freedom of choice", https://arxiv.org/abs/1703.00779 :
   "if w is a process function, then w∘f has a fixed point for every local operation f", and
   Theorem 1 (Unique fixed points): "Given a function w: O→I that satisfies condition (2), the fixed
   point of w∘f is unique for every set of local operations f={f1,…,fN}" (with the remark that
   their proof "also holds for continuous and not only discrete variables"). This is the
   existence ⇒ uniqueness direction (our `fixed_unique`), with finitely many parties. Also
   Baumeler–Wolf, "The space of logically consistent classical processes without causal order",
   https://arxiv.org/abs/1507.01714 (N parties, `0≤j<N`), and the 2025 recursive
   characterisation https://arxiv.org/abs/2512.23599 ("Logical consistency can hold if and only
   if, for any choice of local operations f, the system of equations x=w(f(x)) has exactly one
   solution"; the paper speaks of "arbitrary local dimensions and any number of parties", meaning
   finite n). None of these considers infinitely many parties, and I found no paper that does.
   [Absence claim = result of searching, not proof of absence.]

2. **Boolean networks: the conjugate** [cited]. A. Richard, "A fixed point theorem for Boolean
   networks expressed in terms of forbidden subnetworks", https://arxiv.org/abs/1302.6346
   (DMTCS, https://doi.org/10.46298/dmtcs.2978): "The conjugate of f is the network f̃ on V
   defined by ∀x ∈ B^V, f̃(x) = f(x) ⊕ x", "f̃(x) = 0 if and only if x is a fixed point of f", and
   Remark 5: "Each subnetwork of f has a unique fixed point if and only if the conjugate of each
   subnetwork of f is a bijection" (attributed also to P. Ruet, "Local cycles and dynamical
   properties of Boolean networks", Math. Struct. Comput. Sci.; I did not fetch Ruet's paper).
   Background: Shih–Dong, "A combinatorial analogue of the Jacobian problem in automata networks",
   Adv. Appl. Math. 34 (2005) 30–46, https://doi.org/10.1016/j.aam.2004.06.002 ("if a mapping
   from the n-dimensional hypercube to itself has the property that all the boolean eigenvalues of
   the discrete Jacobian matrix … are zero, then it has a unique fixed point").
   *How it relates* [proved-on-paper, my observation]: for binary parties the local interventions
   are the constants, id and negation; constants give subnetworks (subcubes), negations are
   coordinate flips. Exclusivity of F in XOR form, `(s⊕s') ∧ (G s ⊕ G s') ≠ 0`, says precisely
   that the conjugate of every subnetwork of F (and of every coordinate-flip of F) is
   **injective**. In finite dimension injective ⇒ bijective, so exclusive ⇒ PF (this is a
   one-line proof of the finite binary case via Richard/Ruet). In infinite dimension
   injective ⇏ surjective, and our map is exactly an injective conjugate that misses 0
   (`G(E) ⊆ odd-weight finite vectors`, `G = id` off `E`). So the counterexample is the
   "Dedekind-infinite" failure of the Richard–Ruet criterion. Richard's results are stated only
   for finite `V` / `B^n`; I found no infinite-dimensional version.

3. **Set-theoretic (CH / cov(M)) analogues** [searched, none found]. I found no ZFC-vs-CH
   statement in the process-function or Boolean-network literature that our cov(M) result echoes.
   It is now moot: the ZFC map subsumes it. (The paradigmatic infinite "no consistent assignment"
   example in logic is Yablo's paradox, Analysis 53 (1993); I could not fetch it and do not cite
   it as a source; whether Yablo's map is exclusive was not checked [conjectural/unexamined].)
   Hat-puzzle / Gabay–O'Connor style results were not found to be related: those use choice to
   pick representatives of finite-difference classes, whereas our map needs no choice beyond
   the finite/infinite-support split (it is Borel).

**Novelty status:** apparently new (not found after search), with Richard/Ruet's finite
conjugate-bijection criterion as the closest known analogue, of which ours is the infinite failure.

## Remaining
- lift.md / graded.md / Appendix M not edited yet (per instructions): the Appendix M status for
  "infinitely many parties, exclusive ⇒ PF?" should change from "independent-looking / consistent
  counterexample" to "false in ZFC (explicit Borel counterexample); true for continuous w".
- Possible sharpening (open, not attempted): exclusive ⇒ PF for Baire-class-1 / for w with
  finitely many outputs depending on finitely many inputs, etc.
