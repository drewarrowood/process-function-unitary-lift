# Intermediate classes between "continuous" and "Borel" (2026-11-03)

Context: an exclusive map w on 2^ℕ with continuous coordinates is a process function
(`pf_of_exclusive_continuous`, InfiniteCompact.lean). The ZFC map `zfcF` is exclusive with no fixed
point (ZFCCounterexample.lean). This note asks where in between the boundary lies. Each claim is
tagged **[Lean]** (in `lean/PFUL/IntermediateClasses.lean`; axioms propext, Classical.choice,
Quot.sound only, no sorry), **[paper]** (proof given here, not formalized), or **[conjectural]**.
No new external citations are made. "Baire's theorem on class-1 functions" means the textbook fact
that a Baire class 1 map between Polish spaces is continuous on a comeagre set. That fact is
standard but is not fetched or cited here.

Throughout, the reduction (L-232) applies: an exclusive non-PF w exists in a class C (closed under
composition with interventions) iff an exclusive fixed-point-free (FPF) self-map exists in C.

## 1. The exact complexity of zfcF

* **[Lean] `zfcF_not_continuousAt`.** zfcF is continuous at no point. Already coordinate 0 is
  discontinuous everywhere:
  * if s has finite support, padding s with 1s from n onward gives points → s with F₀ = 0 ≠ 1;
  * if s has infinite support, truncating s at n gives points → s with F₀ = 1 ≠ 0.
* **[paper] zfcF is not Baire class 1.** A class-1 map is continuous on a comeagre set (Baire's
  theorem), but zfcF has no continuity points.
* **[paper] zfcF is Baire class 2.** E = {finite support} is Σ⁰₂. Each coordinate of zfcF is a
  Boolean combination of E with a clopen set, so it is Δ⁰₃-measurable, i.e. Baire class 2.
* **Conclusion [paper]:** zfcF is exactly Baire class 2.

## 2. Classes in which exclusive ⇒ fixed point (so ⇒ PF when closed under interventions)

* **[Lean] Finitary maps, `pf_of_exclusive_finitary`.** Suppose each output w(·)_k depends only
  on a finite set T_k of inputs (T_k may vary with k, non-uniformly). Then exclusive ⇒ PF. Such
  a w is continuous, so this is a corollary of the compactness theorem. The finitary hierarchy
  therefore gives nothing new: every counterexample needs some party that reads infinitely many
  others.
* **[Lean] Monotone maps, `exists_fixed_of_monotone`.** Every monotone F : 2^ι → 2^ι has a fixed
  point (Knaster–Tarski, `OrderHom.lfp`), even without exclusivity. So no monotone map is an FPF
  counterexample. Caveat: monotone w is not closed under interventions (negation), so this does
  not say that monotone exclusive w are PFs. That question remains **[conjectural/open]**.
* **[Lean] Splitting lemma, `exists_fixed_of_frozen`.** Let F be exclusive and T finite. Suppose
  that for every b ∈ 2^T the subproblem "freeze T to b, require F(x)_k = x_k for k ∉ T" has a
  solution. Then F has a fixed point.
  * Proof idea: pick a solution x^b for each b. The reduced map b ↦ F(x^b)|_T on the finite cube
    2^T is exclusive, since an exclusivity witness for (x^b, x^{b'}) must lie in T. By the finite
    theorem it has a fixed point b*, and x^{b*} is a fixed point of F.
* **[paper] Finitely many discontinuities, finite defect.** Let F be exclusive and continuous off
  a finite set P. Suppose every p ∈ P has F(p) ⊕ p of finite support. Then F has a fixed point.
  * Proof: choose a finite T containing every supp(F(p) ⊕ p) and separating the points of P.
  * A cube {s_T = b} that misses P is a closed subcube on which the projected map is continuous
    and exclusive, so it has a solution by the compactness theorem applied to the subcube.
  * A cube that contains some p ∈ P has p itself as a solution, because F(p)_k = p_k for k ∉ T.
  * Apply the splitting lemma.
  * The Lean form would need the compactness theorem relativised to subcubes. It is not done.
* **[paper] Constant-on-pieces fails.** Take discontinuity only at 0, F constant (= a_n) on each
  clopen piece U_n = 0ⁿ1·2^ℕ, and F(0) = 1^ℕ. Then no such F is exclusive and FPF:
  * the pairs (x+e_n, x) with x ∈ U_m, m > n, force (a_m)_n = (a_n)_n;
  * the pair (0, e_n) forces (a_n)_n = 1;
  * together these give a_0 ∈ U_0, so U_0 contains a fixed point.

## 3. Baire class 1: open

**Open question [conjectural].** Is there an exclusive FPF map of Baire class 1 on 2^ℕ? Variants:
Δ⁰₂-measurable, piecewise continuous, a single discontinuity point with infinite defect, or
continuity on a comeagre set. The results above only narrow the target.

* §2 rules out finitely many discontinuities with finite defect.
* §1 shows that the ZFC example is far from class 1, since it is nowhere continuous.

Structural facts for any exclusive F **[paper]**:

* W_n = {s : F(s)↾n = s↾n} is the graph of a function of the tail s↾[n,∞), because finite
  subnetworks are PFs.
* The W_n are decreasing and nonempty, and their intersection is the set of fixed points.
* cl(W_T) ⊆ W_T ∪ Disc(F), where Disc(F) is the set of discontinuity points of F.
* So a counterexample needs every accumulation point of the W_n to be a discontinuity point
  that the W_n leave.

Attempts recorded:

* **Yablo map** F(s)_k = [s_j = 0 ∀ j > k]. It is class 1 and FPF, but not exclusive: the pair
  (0, 1^ℕ) has no witness.
* **"Next-one distance" triangular maps** F(s)_k = h_k(min{j > k : s_j = 1} − k). These are class
  1. With h translation-invariant, FPF forces h = Yablo, which is not exclusive **[paper]**.
  With h_k(d) = [k ∈ K, d ≥ gap_K(k)], the set 1_K is a fixed point.
* **Brute force (evidence only).** Rules F(s)_k = r(s_{k−1}, s_k, s_{k+1}, z_k) with
  z_k = [tail after k is zero] and s_{−1} = 1. All 2¹⁶ rules were tested on prefixes of length 9
  with tails 0, 1, (01), (10), (110), (100). 16,896 rules were FPF on the test set and 0 were
  exclusive. Script: /tmp/cls1/s.py (scratch, not committed).

Leaning: **[conjectural]** a class-1 counterexample, if one exists, must have a discontinuity
set that is infinite, or has infinite defect, and must use non-local information. I do not have
a proof either way.

## 4. Uncountably many parties

**[paper]** For any infinite ι an exclusive FPF map exists in ZFC:

* embed ℕ ↪ ι;
* run zfcF on the ℕ-coordinates;
* output a constant on the other coordinates.

For pairs that agree on ℕ, any differing coordinate off ℕ is a witness. Otherwise zfcF supplies
one. There are no fixed points because zfcF has none. Topological classes (Baire class, Polish)
do not apply directly for uncountable ι.

## 5. Update (2026-11-03, second pass): everything above is now in Lean

New file `lean/PFUL/BaireClasses.lean`. Every theorem uses only propext, Classical.choice and
Quot.sound, with no sorry, checked with `#print axioms`. Every **[paper]** tag in §§1–4 except
the structural remarks in §3 is now discharged. `BaireOne f` means f is a pointwise limit of
continuous maps; for Bool-valued maps on 2^ℕ this is Baire class 1.

* §1, exact complexity:
  * `finSupp_isFσ`: E is a countable union of closed sets.
  * `zfcF_measurable`, `zfcF_borel_measurable`: zfcF is Borel.
  * `zfcF_coord_baireTwo`: each coordinate is a pointwise limit of class-1 maps, i.e. class 2.
  * `exists_continuousAt_of_baireOne`: Baire's theorem for Bool-valued class-1 maps on a Baire
    space. Every nonempty open set contains a continuity point. This is proved here from
    Mathlib's `dense_iUnion_interior_of_closed`, so it is no longer an uncited textbook fact.
  * `zfcF_coord0_not_baireOne`, `zfcF_not_baireOne`: zfcF is not class 1. Together these give
    **exactly class 2 [Lean]**.
* §2, finitely many discontinuities:
  * `exists_subcube_fixed`: compactness on subcubes. If F is continuous at every point of
    {x = b on T}, the frozen subproblem has a solution. It is derived from
    `pf_of_exclusive_continuous` on the index type {k // k ∉ T}.
  * `exists_fixed_of_finite_discontinuities` **[Lean]**. As noted in its proof, the "separating"
    coordinates turned out to be unnecessary: a cube that contains p ∈ P uses p itself.
* §2, constant on pieces: `exists_fixed_of_piece_constant` **[Lean]**. Formalizing it showed the
  statement is weaker than it looked. Only F(0)_0 = 1 and F constant on {s₀ = 1} are used:
  exclusivity for the pair (0, e₀) forces F(e₀)_0 = 1, and then F(e₀) is a fixed point.
* §4, any infinite party set:
  * `exists_exclusive_fixedPointFree_of_infinite` (any `[Infinite ι]`);
  * `exists_exclusive_not_pf_of_infinite` (ι : Type).
* §3, Yablo map: `yablo_ne`, `yablo_not_exclusive`, `yablo_baireOne` **[Lean]**.

## 6. Class 1: progress on (B)

Status: **still open [conjectural]**. What is now established:

* **[Lean]** A class-1 counterexample F must be continuous on a dense open set in every
  coordinate (`exists_continuousAt_of_baireOne`). Since there are countably many coordinates,
  F is continuous on a comeagre G_δ set.
* **[Lean]** Its set of discontinuities cannot be finite with finite defects
  (`exists_fixed_of_finite_discontinuities`).
* **[paper] Triangular reformulation.** Call F triangular if F(s)_k depends only on s↾(k,∞)
  (Yablo-type maps are of this kind).
  * For triangular F, pairs differing in finitely many places always have a witness: take the
    largest differing coordinate.
  * So exclusivity only constrains pairs that differ in infinitely many places.
  * A fixed point is a "backward orbit" s_k = β_k(s↾(k,∞)).
  * Every triangular design I tried fails: Yablo; "next-one distance"; c_k ⊕ [tail = 1_K tail].
    In each case the pair (1_K, t), or (0, 1^ℕ), has no witness.
  * Open sub-question: is there any Borel triangular exclusive FPF map? zfcF is not triangular
    (F(s)_{k+1} reads s_k).
* **[paper] A generalized hotel cannot be class 1 with E closed.** Follow the zfcF template:
  F = 0 off E, and F(t) = e₀ ⊕ rshift(t) on E.
  * The cross pairs force E to be closed under flipping coordinate 0, and under flipping
    coordinate k whenever t_{k−1} = 1.
  * Starting from 0 ∈ E, this generates e₀, e₀+e₁, … → 1^ℕ.
  * So a closed E contains 1^ℕ, which is a fixed point.

Not attempted or not reached: a transfinite-derivative (Cantor–Bendixson style) argument
combining the comeagre continuity set with `exists_subcube_fixed`. The obstacle is that the
discontinuity set of a class-1 map can be dense, so no subcube is free of discontinuities, and
the subcube lemma needs continuity on the whole cube.

## 7. Third pass (2026-11-03): triangular maps, lazy cloakroom, H.19.4

* **Triangular maps [Lean, `lean/PFUL/Triangular.lean`].**
  * `exists_fixed_of_eventually_good`: if some history is consistent at every coordinate ≥ n,
    a fixed point exists (repair from the top down).
  * Hence `infinite_bad_of_fixedPointFree`: every history of a fixed-point-free triangular map
    is inconsistent at infinitely many coordinates.
  * `exists_fixed_of_triangular_continuous`: continuous triangular maps always have a fixed
    point, even without exclusivity. So Yablo's discontinuity is forced.
  * `triangular_witness_of_finite_diff`: exclusivity is automatic for pairs that differ in
    finitely many coordinates.
  * `witness_good_bad` (any binary exclusive F): a witness k is consistent for exactly one of
    the two histories. In particular, the pair (u, F(u)) needs some k ∈ bad(u) with
    F(F(u))_k = F(u)_k.
* **Search (evidence only).** I searched triangular maps of the form
  β_k(a) = [a finitely supported] ⊕ g(a_{k+1}, a_{k+2}, a_{k+3}), with g a translation-invariant
  window rule. FPF forces g(000) = 0 and the backward window map to have 000 as its only cycle.
  Every such g fails exclusivity on eventually periodic test pairs with prefixes up to length 5
  (0 survivors). In fact this window family is ruled out on paper: with g(000) = 1, which
  finite supports need, some nonzero cycle gives an infinite-support fixed point. Script:
  /tmp/tri/s.py (scratch).
* **Status of class 1 / Borel triangular: still open [conjectural].** No construction, and no
  proof that one is impossible.
* **Lazy cloakroom [Lean, `lean/PFUL/LazyCloakroom.lean`]:** `lazy_unitary_all`,
  `lazy_converse_fails`, `not_free_lazy`.
* **H.19.4** was already in Lean from Round 13 (`isPureHilbert_of_isPure`, L-191). It covers
  three binary parties and arbitrary Hilbert ancillas, with no separability assumption. The
  "paper only" tags in lift.md (Round 12 history line) and graded.md §87 were stale and are now
  updated.

## 8. Class 1: countable-perturbation maps (Round of 2026-11-02)

**Reduction (proved on paper).** Look at maps F that equal a constant c off a set S and are
arbitrary on S. Conjugating by s ↦ s⊕c lets us take c = 0 and write F(s) = z(s) on S.
* If such an F is exclusive and fixed-point free, then: 0 ∈ S; z(s) ≠ s; and for every
  s ∈ S the box s ⊕ cube(supp z(s)) lies inside S. The box condition comes from the pairs
  (s, t) with t ∉ S. If S is countable, every z(s) has finite support.
* zfcF is exactly this shape, with S = E the finitely supported sequences. E is countable and
  dense, and that is the obstruction to class 1.
* If S is **countable and closed**, every such F is Baire class 1. Proof: any subset of a
  countable closed set is F_σ, and it is also closed ∩ G_δ, so each set {F_k = 1} is Δ⁰₂.
  So a class-1 counterexample of this form would need only a scattered S that is closed
  under boxes.

**Search evidence (conjectural, not a proof).** I used SAT (pysat/CaDiCaL,
code/pf_search/countable_closed_sat.py) with S = {supp ≤ K} and locally bounded z, meaning
max z(s) ≤ max supp(s) + X. König's lemma makes any infinite solution show up as SAT at every
N. UNSAT is the result for:
* K=2, X≤3: from N=6;
* K=3, X≤2: from N=6; X=3 from N=9;
* K=4, X≤1: from N=6; X=2 from N=8.
The larger X are SAT only for small N. These results suggest that box closure forces
unbounded support, i.e. a dense S as in zfcF.

**Failed candidate (refuted on paper).** I tried F(s) = 1^∞ except F(0^n1^∞) = 1^∞ with
zeros at n−1, n. It is fixed-point free, and random sampling found no violation. It is **not
exclusive**: s = 0^n1^∞ and t = 0^{n−1}10 1^∞ have D = {n−1, n}, where F(s) = 0 and
F(t) = 1. This is the box condition failing.

**Earlier window designs.** The single-discontinuity window family φ_j with a d≥2 rule got
down to 2 bad pairs per 300k samples but never to 0.

Status: the class-1 / Borel-triangular question is still **open**. Conjecture: an exclusive
map that is constant off a countable closed set has a fixed point.
