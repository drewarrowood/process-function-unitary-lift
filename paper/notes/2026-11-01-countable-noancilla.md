# Countable alphabets without ancillas (L.4(b)): partial result (Nov 1 2026)

Question. Finitely many parties, countable alphabets O_k ≃ I_k (infinite allowed), no ancillas,
M[s,e] = ∏_k V_k[s_k, w_k(s) + e_k]. If the loop is unitary on ℓ² (matrix M) for every tuple of local
unitaries V_k on ℓ²(I_k) → ℓ²(O_k), must w be a process function (PF)?

**Result: partial.** Uniqueness of fixed points and several existence cases are proved. Existence in general
is still **open**. I found neither a proof nor a counterexample.

## 1. Where the finite proof breaks

The finite proof (`PFUL.NoAncilla.unitary_noAncilla_iff_pf`) has three steps:
(a) unitary for all V ⇒ exclusivity, via the Gram identity and an explicit witness;
(b) exclusivity ⇒ N(f) ≤ 1;
(c) Σ_f N(f) = #f ⇒ N(f) ≥ 1.
Steps (a) and (b) survive on countable alphabets (§2). Step (c) is the only step that fails: #f is infinite,
and averaging gives nothing. What fails is *existence* of a fixed point. Uniqueness is fine.

## 2. What is proved

**P1 [proved, paper; rigorous].** Unitary for all V ⇒ pairwise exclusivity.
- If Φ is unitary with ⟨δ_r, Φ δ_c⟩ = M[r,c], the rows of M are the conjugates of Φ†δ_r, so they are orthonormal.
- Row Gram identity on ℓ²: (MM†)[s,s'] = ∏_k ⟨row_{s_k} of V_k shifted by w_k(s), row_{s'_k} of V_k shifted by w_k(s')⟩.
  The sum over e ∈ ∏I_k factorises into a finite product of absolutely convergent series, because each factor is
  an inner product of two ℓ² vectors.
- The finite witness carries over unchanged:
  - the Householder reflection 1 − 2vv†/‖v‖² with v = 2e_p + e_{p+δ}, which is finitely supported and so unitary on ℓ²;
  - the permutations swap(e s_k, e s'_k + δ) ∘ e, which are unitary on ℓ².
  Every factor is then nonzero, exactly as in `exclusivity_of_unitary_noAncilla`.
- Not in Lean: the ℓ² Gram identity is not formalised for this layout.

**P2 [proved, Lean].** Exclusivity ⇒ every intervention has at most one fixed point. This holds on any alphabets
(`PFUL.FiniteBox.fixed_unique`).

**P3 [proved, paper; rigorous].** Unitary for all V ⇒ every *bijective* intervention has exactly one fixed point.
- Take V_k = permutation matrix of a bijection σ_k : O_k → I_k.
- Column e of M is then a 0/1 vector. Its squared norm is N(f) for f_k = σ_k^{-1}(· + e_k).
- A unitary has unit columns, so N(f) = 1. Every tuple of bijections I_k → O_k has this form (take e = 0).
- Corollary: N(f) = 1 whenever each f_k restricted to J_k := range(w_k) is injective and
  |I_k \ J_k| = |O_k \ f_k(J_k)|. Fixed points only see f on J_k, so f can be replaced by a bijection that
  agrees with it on J_k.

**P4 [proved, Lean; any alphabets, no finiteness].** Finite-box lemma (`PFUL.FiniteBox.existsUnique_of_box`).
- Statement: if w is exclusive and F(s) = f(w(s)) maps some nonempty finite box ∏B_k into itself, then f has
  exactly one fixed point.
- Proof:
  1. Restrict w to the box. The inputs are T_k = {w_k(s) : s in the box}.
  2. The restriction is exclusive on finite alphabets.
  3. Apply the finite counting theorem `ExclusivityCount.exclusive_imp_existsUnique`. Its proof needs no |I| = |O|:
     Σ_f N(f) = ∏|O_k| · ∏|O_k|^{|I_k|−1} = #f for any finite sizes.
- Conversely, a fixed point s gives the one-point invariant box {s} (`box_of_fixed`).
- So for exclusive w, *f has a fixed point iff F has a nonempty finite invariant box.*

**P5 [proved, Lean].** Exclusive w where every w_k has finite range ⇒ w is a PF, on arbitrary alphabets
(`PFUL.FiniteBox.pf_of_exclusive_finiteRange`).
- Proof: B_k = {o0_k} ∪ f_k(range w_k).
- More generally, f has a fixed point whenever every f_k has finite image on range(w_k), by the same box.

**Combined [proved, paper, from P1 + P5].** If every w_k has finite range, then on countable alphabets without
ancillas, "unitary for all local unitaries" ⇔ PF. Here ⇐ is the countable ℓ² theorem with trivial ancillas.
This covers in particular:
- every case where all but one party has a finite alphabet: the remaining party's w_k depends only on finite
  alphabets, so its range is finite;
- every w with finitely many distinct input values per party.

## 3. What is left (open)

A counterexample must have all of the following:
- w exclusive;
- some w_k with infinite range, which needs at least two parties with infinite alphabets;
- at least 3 parties (two parties: exclusivity forces one w_k constant, hence a PF);
- an intervention f such that:
  - every f-orbit box is infinite, i.e. F(s) = f(w(s)) has no finite invariant box;
  - some f_k has infinite image on range(w_k);
  - f is not equivalent to a bijection on the ranges (P3);
- and still M unitary for *all* local unitaries, not only permutations.

Ideas tried, not completed:
- *Slice reduction (heuristic).* Fix party C's output c. The AB slice is an exclusive two-party map, so it has a
  unique solution (a(c), b(c)). Fixed points of f are then the fixed points of g(c) = f_C(w_C(a(c), b(c))).
  A counterexample needs g to be fixed-point free, like c ↦ c + 1, while exclusivity holds across slices.
  Exclusivity across pairs with c ≠ c' is very restrictive. Simple designs where A and B each depend only on c
  collapse to causal (PF) maps. I did not find a Lugano-type infinite design.
- *Proof via general unitaries (heuristic).* Column norms with general V give Σ_s ∏_k P_k[s_k, w_k(s)+e_k] = 1
  for every unistochastic P_k = |V_k|². These are doubly stochastic. A non-injective deterministic f is not a
  limit of such matrices on the relevant inputs: orthogonal columns cannot both concentrate on one row. So column
  norms do not obviously reach non-injective f. Row orthogonality gives only exclusivity.

Status labels:
- P2, P4, P5 are machine-checked (`lean/PFUL/FiniteBox.lean`, standard axioms only).
- P1 and P3 are paper proofs, rigorous but not in Lean.
- §3 is heuristic exploration.
