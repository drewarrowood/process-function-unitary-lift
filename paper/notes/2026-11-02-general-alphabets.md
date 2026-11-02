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
