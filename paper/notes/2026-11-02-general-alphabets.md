# 2026-11-02 — General alphabets: how far the PF/exclusivity/unitarity results extend

Lean file: `lean/PFUL/GeneralAlphabets.lean` (namespace `PFUL.General`), added to the `PFUL`
lib roots. `lake build` succeeds; no `sorry`. Every theorem below reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`
(`exclusive_not_pf_of_empty` uses no axioms).

## (1) Combinatorial: exclusivity ⇔ process function, arbitrary types

`PFUL.General.exclusive_iff_pf`:
`[Finite ι] [∀ k, Nonempty (O k)]` ⊢ `Exclusive w ↔ ∀ f, ∃! s, ∀ k, f k (w s k) = s k`.

Hypotheses actually used:
* **finitely many parties** (`Finite ι`): the ⇒ direction is the party-by-party induction
  `FiniteBox.existsUnique_of_exclusive` (Finset induction). The ⇐ direction
  (`Countable.exclusivity`) needs nothing about ι beyond what the statement mentions.
  Whether exclusivity ⇒ PF fails for infinitely many parties was not settled here
  (no Lean counterexample attempted; Yablo-style candidates I tried are not exclusive).
* **nonempty output alphabets**: needed for ⇒ only (to seed the induction); necessary, see
  `exclusive_not_pf_of_empty` (one party, `I = O = Empty`: vacuously exclusive, the empty
  intervention has no fixed point).
* Nothing else: no `Fintype`/`Countable`/group/decidability on any `I k`, `O k`
  (decidable equality is supplied classically inside the proof).

## (2) Quantum side on arbitrary discrete index sets (ℓ²(T), T any type)

ℓ²(T) is Mathlib's `lp (fun _ : T => ℂ) 2`, with orthonormal basis `lp.single`; T may be
uncountable (an `example` instantiates the copy-gadget theorem with alphabets `ℝ`, discrete).
All `Countable` hypotheses of the countable results are removed:

* `hasSum_pi_prod_any` — absolutely summable product sums factor over a finite product, any
  index types. Proof: supports of absolutely summable families are countable; reduce to the
  countable lemma via `hasSum_subtype_iff_of_support_subset` and `Equiv.subtypePiEquivPi`.
* `tsum_prod_eq_one_anc_any` — column identity `∑' r, ∏ k, p k (w r.1 k) (r.1 k, r.2 k) = 1`
  for a process function `w` and probability vectors `p k i` on arbitrary `O k × Y k`
  (assumes `Nonempty (I k)`, automatic where used). Proof: each `p k i` has countable support;
  starting from a countable seed, iterate "add the supports of `p k (w s k)` for `s` in the
  current box" (`step`, `cl`); the closure is a countable box `C` with
  `supp p k (w s k) ⊆ C k` for `s ∈ C`. On `C`, with inputs restricted to the range of `w`,
  the restricted `w'` is still a process function, so the countable theorem gives sum 1 over
  the box. Upper bound: every finite set of terms lies in such a box (seed it with them);
  lower bound: the box sum is ≤ the full sum. (The infinite-product-measure proof does not
  carry over directly since an uncountable union of null cylinders need not be null; the
  closure argument avoids this.)
* `induced_unitary_l2_any` (PF ⇒ induced map is a unitary `ℓ² ≃ₗᵢ ℓ²`, general ancillas),
  `unitary_l2_iff_pf_any` (copy gadget, `X = O`, `Y = I`),
  `exclusive_of_unitary_l2_any` (P1: unitary for all no-ancilla local unitaries ⇒ exclusive),
  `unitary_l2_noAncilla_iff_pf_any` (no ancillas, `e : ∀ k, O k ≃ I k`). Same proofs as the
  countable versions, with the two lemmas above substituted.

**Group law.** Still in the statements: kernels are evaluated at `w f k + e k`, and the gadget
and witnesses use `+`/`-`. What the proofs use is only (i) `c ↦ a + c` is a bijection for each
`a` (shift invariance of sums), and (ii) in the no-ancilla witness, a bijection `τ` with
`τ x' - a' = τ x - a` (one transposition) or a shift by `a - a'`; i.e. the family of shifts
acts simply transitively. Restating with an arbitrary family of bijections
`σ_a : I k ≃ I k` (and corresponding gadget) should go through, but was **not** formalized;
the cardinality condition `O k ≃ I k` remains essential for the no-ancilla direction.

## (3) Continuous alphabets (L²(ℝ) etc.) — not formalized

For continuous alphabets the discrete statement does not literally make sense. There are no
basis-vector histories: `L²(ℝ)` has no orthonormal basis indexed by points of ℝ, so the
"matrix" `M r c = ∏ V(...)(w r + c)` is at best a distribution kernel, and composing kernels
along `w` requires `w` to be measurable and the pushforwards to make sense. The fixed-point
characterisation is also not measure-theoretically robust: the fixed points of `s ↦ f(w s)`
form a set that is generically Lebesgue-null (a single point in ℝⁿ), so "exactly one fixed
point" for every deterministic intervention is invisible to `L²`-level unitarity, and
modifying `w` on a null set changes the PF property without changing any induced operator.
The right formulation is operator-theoretic: (a) state the induced map on `L²(∏ O_k, μ)` via
local unitaries/channels given as measurable kernels or as unitaries commuting with the
translation group (Weyl operators), and require unitarity for all of these; (b) replace
"unique fixed point" by an a.e./measure condition — e.g. that for a.e. (or every measurable)
intervention the fixed-point map has a measurable inverse with the right Jacobian, as in the
existing `Continuous*.lean` work (τ bijective with constant-fibre condition, Jacobian
identity). The existing repo files treat the translation-covariant group case; a general
statement for arbitrary standard Borel alphabets is open and probably needs the direct-integral
(rather than basis) picture. No claim is made here.

## Honest scope

Proved: finitely many parties, arbitrary discrete alphabets (any cardinality), group law kept.
Not done: infinitely many parties; group law → general bijections; continuous alphabets.

## Addendum (D): bijection law in place of the group law; infinitely many parties

**Lean, `lean/PFUL/BijectionLaw.lean`** (standard axioms only, no sorry). The loop reads
`σ k (w f k) (e k)` with `σ k : I k → Equiv.Perm (I k)` arbitrary (the group case is
`σ k a = Equiv.addLeft a`, free by `free_addLeft`). The results:
- `induced_unitary_l2_σ`: PF ⇒ unitary needs **no condition on σ**.
- `unitary_l2_iff_pf_σ`: copy-gadget converse, assuming σ is **free** (`σ a c = σ a' c → a = a'`) and `[Nonempty O]`. The output alphabets need no algebra because the gadget uses `Equiv.swap`.
- `exclusive_of_unitary_l2_σ` and `unitary_l2_noAncilla_iff_pf_σ`: the no-ancilla version, assuming σ free, `e : O ≃ I` and `Nonempty O`. Nonempty O is needed: if O is empty the ℓ² space is trivial.

A simply transitive action is free. Transitivity is never used, so "simply transitive" weakens to "free".
Freeness cannot simply be dropped. If σ a = id for every a, the loop ignores w, so every w (PF or not) gives a unitary. This is argued in prose only, not in Lean.

**Infinitely many parties, `lean/PFUL/InfiniteParties.lean`.** For any ι:
- `fixed_unique`: exclusivity gives at most one fixed point.
- `exists_exclusive_not_pf_iff`: an exclusive non-PF w exists iff there is a fixed-point-free exclusive self-map F of ∏ O_k.
- Equivalently (O_k = Bool, F = s ⊕ a(s)): there is a : 2^ι → 2^ι \ {0} such that for all s ≠ s′, a(s) and a(s′) differ at some coordinate where s and s′ differ.

Status: **open; no counterexample and no proof.**
- Near misses: a(s) = s fails only at s = 0, and a(s) = ¬s fails only at s = 1.
- The Yablo map fails exclusivity on a pair (s, finite truncation of s).
- Class-constant xor patches (c_E chosen by tail class) fail across classes.
- Injective single-flip maps are impossible by cardinality.
- Conjecture: PF holds for continuous w with finite alphabets (by compactness). The discontinuous/choice case is open.

Nothing in (D) is pushed.

## Addendum (E): infinitely many parties — continuous case proved; consistent counterexample

**(1) Continuous case, Lean `lean/PFUL/InfiniteCompact.lean`, `pf_of_exclusive_continuous`**
(standard axioms only). Hypotheses:
- ι is an arbitrary index set;
- the output alphabets O_k are finite, nonempty and discrete;
- the input alphabets I_k are discrete;
- each coordinate s ↦ w s k is continuous in the product topology;
- w is exclusive.

Conclusion: every intervention f (arbitrary local maps, which are automatically continuous on discrete I_k) has exactly one fixed point.

Proof:
- **Truncations.** The truncation of w itself is not the right object. The right object is the conditional restriction: fix a finite T and an arbitrary background t outside T, and set G(u) = (f∘w)(u ⊔ t)|_T.
  - G is exclusive. If u ≠ u′, exclusivity of w applied to u ⊔ t and u′ ⊔ t gives a party k where these differ, and such a k must lie in T.
  - So `exclusive_iff_pf` (finitely many parties) gives G a fixed point.
- **Compactness.** Hence the clopen sets C_k = {s : f_k(w(s)_k) = s_k} have the finite intersection property in the compact space ∏O_k (Tychonoff), so their intersection is nonempty.
- **Uniqueness** follows from exclusivity.

Continuity is used only to make the C_k closed.

**(2) Discontinuous case: a counterexample exists under cov(M) = 𝔠 (e.g. CH or MA); ι = ℕ, all alphabets Bool.**
Paper proof only, not in Lean. By `exists_exclusive_not_pf_iff`, we need F : 2^ℕ → 2^ℕ with no fixed point that is exclusive.

- **Construction.** Let B = P(ℕ)/fin. Take F constant on E₀-classes (finite-difference classes): F(s) = rep(g([s])) for some g : B → B.
- **Requirements on g.**
  - Same-class pairs are automatically fine: F(s) = F(s′), and they differ somewhere.
  - No fixed point ⇔ g(x) ≠ x for all x.
  - Cross-class pairs are fine ⇔ for x ≠ y, (x+y) ∧ ¬(g x + g y) ≠ 0 in B. Reason: the difference set d(s,s′) ranges over all finite modifications of R = r_x Δ r_y, and some k ∈ d with F(s)_k = F(s′)_k exists for every such d iff R ∖ (c_x Δ c_y) is infinite.
- **Building g.** Enumerate B as (x_α)_{α<𝔠} and choose z = g(x_α) by recursion. Each constraint "[z] ≠ x_α" or "(x_α+x_β) ∧ ¬([z]+g x_β) ≠ 0" (for β < α) forbids a set of the form {z : z ≡ b on R mod finite} with R infinite. Such a set is meager in 2^ℕ.
  - At stage α only |α| < 𝔠 meager sets are forbidden, so under cov(M) = 𝔠 an admissible z exists.
  - Under CH there is also an elementary choice: pick pairwise disjoint infinite Q_n ⊆ R_n and set z = ¬b_n on Q_n.
- **Conclusion.** Consistently (Con(ZF) ⇒ Con(ZFC + an exclusive non-PF w with countably many binary parties)), exclusivity does not imply PF for infinitely many parties.

**Gaps.**
- (a) I have no ZFC construction and no ZFC impossibility proof. The question may be independent: one would expect no counterexample in models where every set has the Baire property, but this is unproved.
- (b) An affine reduction exists. It suffices to find an F₂-linear L on F₂^ℕ with u ∧ L u ≠ 0 for every u ≠ 0 and L not surjective (then a(s) = L s + c with c ∉ ran L). Continuous L is ruled out by (1). I did not find a discontinuous L.
- (c) The CH construction is not formalised in Lean, since that would need CH or cov(M) = 𝔠 as a hypothesis plus transfinite recursion.
