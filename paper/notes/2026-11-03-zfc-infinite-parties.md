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

## Literature (step 1)
Not needed for the result; I make no claims of prior appearance and cite nothing. The CH →
ZFC-by-Bernstein route (step 2) was moot once the explicit construction was found. Whether this
construction is already known in the indefinite-causal-order literature
(Baumeler–Wolf process functions with infinitely many parties) was **not checked** [conjectural
that it is new].

## Remaining
- lift.md / graded.md / Appendix M not edited yet (per instructions): the Appendix M status for
  "infinitely many parties, exclusive ⇒ PF?" should change from "independent-looking / consistent
  counterexample" to "false in ZFC (explicit Borel counterexample); true for continuous w".
- Possible sharpening (open, not attempted): exclusive ⇒ PF for Baire-class-1 / for w with
  finitely many outputs depending on finitely many inputs, etc.
