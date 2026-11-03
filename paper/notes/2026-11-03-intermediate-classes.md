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
