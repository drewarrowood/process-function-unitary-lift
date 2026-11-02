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

## 4. Resolution (2026-10-31): the countable no-ancilla converse holds

**Theorem.** Let ι be finite, and give each I_k a countable abelian group structure, with O_k ≃ I_k. Then the induced map is unitary on ℓ² for every family of local unitaries without ancillas (X_k = Y_k = Unit) if and only if w is a process function.
- Lean: `PFUL.Countable.unitary_l2_noAncilla_iff_pf` in `lean/PFUL/NoAncillaL2.lean`.
- Axioms: only propext, Classical.choice, Quot.sound. No sorry, no native_decide.

**Key new lemma (counting-free): exclusive ⇒ PF, on any alphabets.**
- Lean: `PFUL.FiniteBox.existsUnique_of_exclusive` in `lean/PFUL/ExclusiveInduction.lean`. It uses finite ι, DecidableEq, and nonempty O_k. No cardinality assumptions.
- Uniqueness is P2 (`fixed_unique`).
- Existence goes by induction on a set T of "active" parties (`exists_partial_fixed`). The parties outside T are frozen at given values u.
  - Add a party n to T.
  - For each value c of party n, the induction hypothesis gives a configuration s(c): it is fixed on T, has s(c)_n = c, and equals u elsewhere.
  - Claim: g(c) = f_n(w_n(s(c))) does not depend on c.
    - Take c ≠ c′. Exclusivity gives a party k where s(c) and s(c′) differ but w_k agrees.
    - k cannot lie outside T ∪ {n}, because both configurations equal u there.
    - k cannot lie in T, because both configurations are fixed there and w_k agrees, so their values at k are equal.
    - So k = n, and w_n agrees, so g(c) = g(c′).
  - Set c* = g(c₀). Then s(c*) is fixed on T ∪ {n}.
- This also gives a proof of the finite case that does not use counting (cf. N.1).

**P1 is now in Lean: unitary for all V ⇒ exclusive.**
- Lean: `exclusive_of_unitary_l2`.
- Suppose exclusivity fails at s ≠ s′. Then at every party k, either s_k ≠ s′_k and w_k(s) ≠ w_k(s′), or s_k = s′_k.
- `local_witness` builds a local unitary at each k for which the row-overlap factor ∑_i V(s_k, w_k(s)+i) · conj V(s′_k, w_k(s′)+i) is nonzero:
  - **Case s_k = s′_k and w_k(s) ≠ w_k(s′):** use a real 2×2 rotation (3/5, 4/5) on {p, p + w_k(s) − w_k(s′)} with p = e(s_k), and the identity elsewhere.
    - Row p is nonnegative, so the overlap is a nonnegative series.
    - It contains the term (4/5)(3/5) > 0, so the overlap is positive.
  - **Otherwise:** use a permutation e followed by a transposition, chosen so that σ(s′_k) − w_k(s′) = σ(s_k) − w_k(s). The overlap is then 1.
- The row Gram sum of the induced map factorises into the product of these local overlaps, by `hasSum_pi_prod`. So the product is nonzero.
- But orthonormal rows (`rows_of_lie`, read off from the isometry Φ) force the Gram sum to be 0, since (s, ·) ≠ (s′, ·). Contradiction.

**What is rigorous and what is heuristic.**
- Everything in this section is machine-checked.
- L.4(b) is closed for countable abelian-group alphabets with |O_k| = |I_k|, no ancillas, and finitely many parties.
- The ℕ-Lugano search mentioned in §3 is heuristic only. It found w = (c·[b=0], a·[c=0], b·[a=0]), which is exclusive on the box N=12, and every f tested there had a unique fixed point. That is now explained by the theorem, so no counterexample with three or more parties exists in this setting (Direction B is ruled out).
