# Audit and converse notes, 31 Oct 2026 (draft appendix material, not in lift.md)

Status labels: **[proved]** = paper proof given here, checked numerically/exactly as stated; **[exact]** = exact-arithmetic
computation; **[numerical]** = float64; **[open]**. Nothing here has been peer reviewed. Scripts and logs:
`code/audit_2026-10-31/`.

## 1. Lean axiom audit [exact; Lean 4.34.1, Mathlib v4.34.1 at d13f23b]

- `lake build` of all three libraries (PFUL, Legacy, MathlibPR) from the Mathlib cache: success, 8987 jobs, 0 errors,
  0 "declaration uses 'sorry'" warnings (only deprecation/style warnings). The Mathlib package checkout differs from its
  pinned commit only by 7 deleted files under `scripts/bench/` (no Lean sources).
- Text search of every project `.lean` file: no `sorry`, `admit`, `axiom`, `implemented_by`, `extern` or `unsafe`.
  `native_decide` occurs only in the Legacy files `Gaps.lean`, `Cancel.lean`, `Full.lean`, `StinespringBoundary.lean`.
- **All-declarations audit** (`AuditAll.lean.txt`: a metaprogram running `Lean.collectAxioms` on every theorem whose
  module is in the project, rather than a hand-picked list):
  - PFUL + MathlibPR: **779 theorems, all depend only on `propext`, `Classical.choice`, `Quot.sound`.**
  - Legacy (each file audited separately, since `Full` and `Gaps` cannot be imported together): Lift 12/12, GramGeneral
    27/27, ComplexGram 15/15 standard. **11 Legacy theorems use `native_decide`** (each pulls in an auxiliary
    `*._native.native_decide.ax_*` axiom, i.e. trusts the compiler): `Full.hadamard_rows_orthogonal`;
    `Gaps.hadamard_rows`, `Gaps.trace_identity_ancilla`; `Cancel.lugano_is_process`, `lugano_lemma`,
    `ident_fails_lemma`, `cycle_fails_lemma`, `lugano_cancellation`, `ident_cancellation_fails`,
    `cycle_cancellation_fails`; `StinespringBoundary.closed_not_every_w`.
    None of these is used by any PFUL theorem (PFUL does not import Legacy). The comment headers of `Full.lean`
    ("no sorry") and `StinespringBoundary.lean` ("no sorry, no axiom") are literally true for `sorry` but the latter
    should say it uses `native_decide`.
- Named main theorems (`MainAxioms.lean.txt`, log `lean_main_axioms.log`), all standard axioms only: `exclusivity`,
  `induced_mul_conjTranspose(_complex)`, `induced_unitary`, `induced_conjTranspose_mul(_of_colnorm)`,
  `Column.sum_prod_eq_one`, `Countable.{tsum_prod_eq_one, induced_colnorm, induced_rows, induced_unitary_l2,
  valid_born_l2}`, `valid`, `valid_kraus`, `valid_instrument`, `Choi.{bornC_anc_eq_one, afnb_iff_density,
  isCP_iff_choi, validity_package}`, `Counterexample.{purification_conjecture_false, purification_conjecture_false_choi,
  isPure_Vsb, valid_pcl, pcl_not_mem_convexHull, isPureHilbert_Vsb, valid_normalCPTP_Vsb, isPurePM_choiMat_Vsb}`.
- `decide` / `decide +kernel` (LemmaH, Counterexample*) are kernel-checked and add no axioms.
- **Not covered by the audit:** whether the Lean definitions faithfully express the paper's notions (an axiom audit
  cannot see this). **The (⇒) half of Theorem 1.2 (copy gadget) is not formalised in Lean**; only (⇐) is.

## 2. H.12.1 exact re-check in sympy [exact]

`h12_exact_sympy.py` (log `h12_exact_sympy.log`) rebuilds the board from the m_o(z) table printed in lift.md H.12 (not
from `cex_phases.json`) and uses sympy symbolic arithmetic (Q(ζ₈) via `I`, `sqrt(2)`, `exp(-iπ/4)`) instead of the
hand-written Q8 class of `exact_cex.py`.
1. All eight U_o are exactly unitary (entries in Z[i]/8).
2. All **2,232** forbidden Pauli coefficients of K_{o,o'} vanish exactly (Pauli rule H.8.1). Purity then follows via the
   paper lemmas H.7.1 + H.8.1 + H.8.2 (as before; Lean's `isPure_Vsb` does not use them).
3. p is real, ≥ 0, columns sum to 1, and all 64 deterministic interventions give total probability exactly 1 (valid).
4. With the facet functional g of `exact_cex.log` (facet 1741): **g·p + g₀ = 1/4 − (3/16)√2 exactly** (< 0); on the 744
   PFs of `pfs744.npy` min = 0, tight on 418. max|g| = 2, so the certified L1 margin is exactly **3√2/32 − 1/8 ≈
   0.0075825**. (Coincidence worth noting: this equals the per-o-averaged LP distance 0.0606602/8 quoted in H.12, i.e.
   (3√2−4)/32; the unaveraged LP value 0.0607 remains a float LP figure, not re-certified here.)
5. **New, direct exact purity spot-check, independent of H.7.1/H.8:** the closed-loop M with exactly unitary local maps
   over Q(i) (Cayley transforms of random rational Hermitian matrices) satisfies M M† = 1 and M† M = 1 **exactly**
   (sympy DomainMatrix over QQ_I): 3 trials without ancillas (64×64) and 2 trials with a qubit ancilla per party
   (512×512): **all 5 trials passed exactly**. Negative control (`neg_control.py`): changing one exponent m_000(000) from
   0 to 1 makes the same exact test fail.
   Scope: finitely many exact samples; this corroborates, but does not replace, the Pauli-rule proof or `isPure_Vsb`.
Not re-checked: the enumeration count 744 (taken from `pfs744.npy`), that g is a facet, the LP distance.

## 3. Converse without ancillas [proved for finite equal local alphabets; numerically corroborated]

Setting: |I_k| = |O_k| = d_k finite (otherwise no ancilla-free local unitaries exist and the question is vacuous),
I_k = O_k = Z_{d_k}, M[s,e] = ∏_k V_k[s_k, w_k(s) + e_k].

**Theorem N.1.** For w : ∏O_k → ∏I_k the following are equivalent:
(i) w is a process function; (ii) M is unitary for every tuple of ancilla-free local unitaries;
(iii) M is unitary for one Haar-random tuple (with probability 1); (iv) pairwise exclusivity: for all s ≠ s' there is
k with s_k ≠ s'_k and w_k(s) = w_k(s').

*Proof.* Row Gram identity (summing over e factorises over parties):
(M M†)[s,s'] = ∏_k Σ_{e_k} V_k[s_k, w_k(s)+e_k] conj V_k[s'_k, w_k(s')+e_k] = ∏_k (V_k T^{δ_k} V_k†)[s_k, s'_k],
δ_k = w_k(s) − w_k(s'), T the cyclic shift. Diagonal entries are always 1 (rows are always unit vectors), and M is
square, so M unitary ⇔ all off-diagonal products vanish.
(iv)⇒(ii): the factor with δ_k = 0, s_k ≠ s'_k is (V V†)[s_k,s'_k] = 0. (This is the Theorem of §1 with trivial ancillas.)
(iii)⇒(iv): if (iv) fails for s ≠ s', every factor has either δ_k = 0, s_k = s'_k (factor 1) or δ_k ≠ 0. For δ ≠ 0, T^δ
is not scalar, so V ↦ (V T^δ V†)[a,b] is a real-analytic function on the connected manifold U(d) that is not identically
zero (diagonal: take v an eigenvector of T^δ; off-diagonal: take v not an eigenvector and u in the direction of the
component of T^δ v orthogonal to v); its zero set is Haar-null. A finite union of null sets is null, so for Haar-a.e. V
the product is nonzero and M is not unitary. (ii)⇒(iii) trivial.
(i)⇔(iv): (i)⇒(iv) is the exclusivity Lemma (`PFUL.exclusivity`). (iv)⇒(i): if s ≠ s' were both fixed points of f∘w,
take k from (iv): s_k = f_k(w_k(s)) = f_k(w_k(s')) = s'_k, contradiction; so N(f) ≤ 1 for every f. And
Σ_f N(f) = Σ_s ∏_k d_k^{d_k−1} = ∏_k d_k^{d_k} = #interventions, so the mean of N is 1 and N ≡ 1. ∎

So: **every PF lifts with no party ancilla (equal alphabets), and every map whose ancilla-free loop is unitary for all
local unitaries is a PF.** Ancillas are not needed for the converse; a single generic draw is a complete test. What the
ancillas buy in the copy gadget is a *deterministic, explicit* witness (column norm = fixed-point count).
Side remark: column norms alone cannot do it without ancillas. Σ_s ∏_k |V_k[s_k,w_k(s)]|² is multilinear in the
unistochastic matrices |V_k|², so it equals 1 on all of them iff N(f) = 1 for all *bijective* f; the 39,576 three-party
binary non-PFs below pass that test, and only the row (orthogonality) conditions detect them.

Evidence: `excl_vs_pf.py` / `.log`: Gram identity to 4e-16 (n=2,3 binary; n=2, d=3,4); exclusivity ⇔ PF with 0
mismatches on all 256 two-party binary maps (12 PFs) and all **16,777,216** three-party binary maps (744 PFs both ways),
and on 300k random two-party ternary maps. `noanc_enum.py` / `.log`: exhaustive one-party d=2,3,4, two-party binary,
three-party binary (all 8^8 maps); every non-PF fails ancilla-free unitarity, either by a permutation intervention or,
for the 12 (n=2) and 39,576 (n=3) maps passing all permutation interventions, by a Haar draw (smallest residual
‖MM†−1‖_F found ≥ 0.016, far above float error ~1e-15). 2M random two-party ternary maps: all non-PFs caught.
Not done: Lean formalisation; exact (non-float) witnesses for the enumerated survivors (the proof makes them unnecessary).

## 4. Converse for countable alphabets [proved (paper) with ancillas; ancilla-free version open]

Finitely many parties, I_k, O_k countable (finite or ℕ), PF = every f has exactly one fixed point (as in
`PFUL.Countable`). Give each O_k a group structure (Z_n or Z).
**Claim C.1.** If w is not a PF, the copy gadget V_k|i,x⟩ = |f_k(i)+x, i⟩ on ℓ²(I_k × O_k) → ℓ²(O_k × I_k) (a bijection of
basis vectors, hence unitary on ℓ²) gives a closed loop with no unitary (indeed no isometric) realisation.
*Proof.* The loop wiring is a permutation, so the entries M[(s,y),(e,x)] = ∏_k V_k[(s_k,y_k),(w_k(s)+e_k,x_k)] are finite
products, no series. Column (0,0) is the indicator of {(s, w(s)) : f(w(s)) = s}, with N(f) ∈ {0,1,2,…,∞} entries. Any
isometry Φ with Φδ_c = M(·,c) needs ‖M(·,(0,0))‖² = 1; but it is N(f) ≠ 1 (for N = ∞ the column is not even in ℓ², so
no bounded operator has these matrix entries). ∎ So with ancillas, Theorem 1.2 holds for countable alphabets:
(⇐) is `PFUL.Countable.induced_unitary_l2` (Lean), (⇒) is C.1 (paper only). Nothing in the finite proof used finiteness
except the target statement "M not an isometry", which C.1 replaces by the column-norm obstruction.
Example of the N = ∞ case: one party, I = O = ℕ, w = id, f = id.
**Where it breaks.** (a) Continuous alphabets: the gadget is still unitary on L² (shear+swap preserves Lebesgue measure,
for measurable f), but basis vectors δ_c are not in L², so "column norm = fixed-point count" has no meaning; one needs a
measure-theoretic replacement (cf. F.5). (b) Without ancillas on countable alphabets: the Gram identity and
"exclusivity ⇒ N(f) ≤ 1" survive, but the averaging step Σ_f N(f) = #f needs finiteness, and there is no Haar measure on
U(ℓ²) (genericity would have to be redone, e.g. with finite-rank perturbations). For two parties exclusivity forces one
of w_A, w_B to be constant, hence a PF, so a countable counterexample to "exclusive ⇒ PF" would need ≥ 3 parties. [open]
