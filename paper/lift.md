# Every process function lifts to a unitary process

**Draft note. Not submitted. Not refereed.** Canonical source of the paper; `lift.pdf` is built from this file.

## Abstract

A process function is a classical map w from the outputs of several parties to their inputs such that every choice of local deterministic interventions has exactly one fixed point. Baumeler, Costa, Ralph, Wolf and Zych showed that every process function extends to a bijection by adding a source and a sink, and left open whether every such bijection quantizes to a valid unitary quantum process; Daher Ahmed and Kunjwal (2026) state this as a conjecture and prove it for a subclass. We give a short argument that it holds for every process function with finite alphabets: the permutation unitary U|o,e> = |w(o)+e, o> composed with arbitrary local unitaries induces a unitary from source to sink. The key combinatorial fact, that two distinct output strings always disagree at some party whose input w assigns equally, is the pairwise-exclusivity property of Dourdent et al. (2026). The philosophical sections read the result as saying that fixed-point consistency is already a quantization condition. The result is a draft: the exclusivity lemma and the identity M M^dagger = 1 (complex amplitudes, any finite number of parties, any finite alphabets, local ancillas) are machine-checked in Lean 4 with Mathlib (theorems PFUL.induced_mul_conjTranspose, PFUL.induced_conjTranspose_mul and PFUL.induced_unitary, the last stating membership in the unitary group; standard axioms only). The step from "unitary under local unitaries" to "valid process" (Appendix A) is also machine-checked: for arbitrary local CPTP maps in Kraus form via their Stinespring isometries (PFUL.valid_kraus), for instruments (PFUL.valid_instrument), and in the Choi/process-matrix form Tr[W(rho (x) 1 (x) C_A (x) ...)] = 1 for all local CPTP Choi matrices, with party ancillas (PFUL.Choi.bornC_anc_eq_one). The two forms are proved equivalent (PFUL.Choi.afnb_iff_density), and Choi's theorem is proved too (PFUL.Choi.isCP_iff_choi). A second part studies stochastic classical processes. Mixtures of process functions are purifiable, and we conjecture that nothing else is. We give exact non-purifiability certificates for E_ex1 and two vertex orbits, several structural lemmas, a counterexample to a natural strengthening, a no-go for certificates that use only the fixed source state, the complete facet list of the 3-party binary process-function hull (29,344 facets in 93 symmetry orbits), and numerical evidence. The conjecture itself remains open; Section 9 states exactly what is proved.

## 1. Result and short proof

**Setting.** Parties k = 1..n. Party k has a finite input alphabet I_k, identified with the cyclic group Z_{|I_k|}, and a finite output alphabet O_k. A process function is w = (w_k): prod O_k -> prod I_k such that for every tuple of local functions f_k : I_k -> O_k the map o -> (f_k(w_k(o)))_k has exactly one fixed point. The source has output space P = prod I_k, the sink has input space F = prod O_k, and

    U |o>_O |e>_P = |w(o) + e>_I |o>_F      (componentwise addition mod |I_k|).

U is a permutation of basis states, hence unitary, for every map w (Baumeler et al. 2019, Theorem 2).

**Lemma (exclusivity).** If w is a process function and s != s' in prod O_k, there is a party k with s_k != s'_k and w_k(s) = w_k(s').

*Proof.* Otherwise, for every k, w_k(s) = w_k(s') implies s_k = s'_k. Define f_k(x) = s_k if x = w_k(s), f_k(x) = s'_k if x = w_k(s') (and arbitrary otherwise); the two clauses agree when w_k(s) = w_k(s'). Then s and s' are two distinct fixed points of the same intervention, a contradiction. (This is the forward direction of Dourdent et al. 2026, Theorem 7.)

**Theorem.** Let V_k be any unitary from I_k (x) X_k to O_k (x) Y_k, with local ancilla spaces X_k, Y_k (|I_k||X_k| = |O_k||Y_k|). Composing U with the V_k (feeding each I_k into V_k and each O_k back into U) gives the operator M from P (x) X to F (x) Y with entries

    M[(s,y),(e,x)] = prod_k V_k[(s_k, y_k), (w_k(s) + e_k, x_k)].

M is unitary.

*Proof.* (M M^dagger)[(s,y),(s',y')] = sum over e, x of the product over k, which factorises as prod_k sum_{e_k, x_k} V_k[(s_k,y_k),(w_k(s)+e_k, x_k)] conj V_k[(s'_k,y'_k),(w_k(s')+e_k, x_k)]. If w_k(s) = w_k(s'), substituting i = w_k(s) + e_k turns the k-th factor into the inner product of rows (s_k,y_k) and (s'_k,y'_k) of the unitary V_k, i.e. a Kronecker delta. If s = s' every factor is of this kind, giving delta_{y,y'}. If s != s', the Lemma gives a party with w_k(s) = w_k(s') and s_k != s'_k, whose factor is 0. So M M^dagger = 1, and M is square, hence unitary.

In the language of Araújo, Feix, Navascués and Brukner (2017, Definition 1), the process |U>><<U| is therefore *pure*. Section 2 spells out why this implies validity for arbitrary local CPTP maps and instruments, including ancillas shared or entangled with outside systems. Fixing the source to |0> and tracing the sink recovers the diagonal process matrix of w.

**Converse (numerical only).** If w is not a process function, the exclusivity property fails (Dourdent et al. 2026, Theorem 7); we have not proved that unitarity then fails in general, but numerically (code/check.py) every non-process function in the 2- and 3-party binary cases fails unitarity for random local unitaries. The "open/closed" contrast is the point: U is a bijection for every w; closing the loop is unitary exactly when w is consistent.

**Checks.** code/check.py enumerates all 12 binary 2-party and 744 binary 3-party process functions, verifies ||MM^dagger - 1|| < 1e-13 for Haar-random local unitaries (with and without qubit ancillas) and for ternary 2-party examples, and verifies that non-process functions fail. Lean status is in lean/STATUS.md.

## 2. From unitarity to validity

Section 1 shows that the lift is *pure* in the sense of Araújo et al. (unitaries in, unitary out). Appendix A derives full process validity from this (any local CPTP maps, local and shared/entangled ancillas, instruments) using Stinespring dilation. Appendix B covers input and output alphabets of different sizes. Appendix C treats stochastic classical processes: mixtures of process functions are purifiable, but a non-deterministic extremal point of the Baumeler–Wolf polytope provably is not (exact certificate).

## 3. Backward causation, before the formalism

The linguistic objection to backward causation is that a cause is, by definition, earlier than its effect. Dummett argued in 1954 and again in 1964 that this is a stipulation about the word, not a discovery about the world. Black's bilking argument is the better objection. If an earlier event is supposed to be the effect of a later one, an agent who sees the earlier event can intervene so as to prevent the later one. Either the agent cannot intervene, which wants an explanation, or the later event was not necessary for the earlier one. Lewis's reply splits the modal: one can, relative to the local facts and the laws, and one cannot, relative to the whole past. That dissolves a verbal paradox. It does not say which histories the laws admit.

General relativity makes the question physical. Gödel's 1949 solution has closed timelike curves. Morris, Thorne and Yurtsever showed that a traversable wormhole, if one could be held open, can be converted into a time machine by relative motion of the mouths. The Cauchy problem on the resulting spacetime is the grandfather paradox in differential equations. Friedman, Morris, Novikov, Thorne and collaborators proposed, in 1990, that only self-consistent solutions occur. Echeverria, Klinkhammer and Thorne then studied a hard-sphere billiard ball on a wormhole. For every "dangerous" initial trajectory they examined, one aimed so that the ball would knock its younger self off course, they found at least one self-consistent continuation, and many initial data admit several, some infinitely many. They did not prove that consistent solutions exist for all initial data, but they found no case without one. Carlini, Frolov, Mensky, Novikov and Solodukhin derived a version of self-consistency from stationarity of the action in a model, and found the same underdetermination. Novikov's principle removes inconsistent solutions. It does not choose among consistent ones. Earman's survey of the classical problem remains the right warning: a consistency condition that is imposed after the dynamics is not a dynamics.

## 4. Three quantum replies, and why none is the criterion

Deutsch's 1991 model asks for a fixed point of the partial trace around the curve. In finite dimension a fixed point exists, so no particular action is forbidden, and the grandfather paradox becomes a mixed state. The cost is nonlinearity. The model clones unknown states. Aaronson and Watrous showed that the computational power is PSPACE. Bennett, Leung, Smith and Smolin argued that the power is an artefact of demanding a fixed point for a distribution that an ordinary preparation would not produce. Tolksdorf and Verch showed that the Deutsch condition can be met to arbitrary precision in quantum field theory on a spacetime with no closed timelike curve at all. A Deutsch fixed point is not diagnostic of a loop.

Lloyd, Maccone and collaborators replace the fixed point by post-selection, the P-CTC model. Inconsistent branches are the ones that fail the post-selection. The grandfather paradox is resolved by the experiment not happening. Process functions sit inside this class: the event list appears conditional on the post-selection succeeding. That is a simulation. It is not an account of why the inconsistent branch was never a physical option. Post-selection is a filter on samples, of the same shape as a measure-zero axiom.

The process-matrix formalism of Oreshkov, Costa and Brukner is the third reply, and the one this note uses. A process is a map from local instruments to probabilities, required to give a probability for every choice of instruments, with no global causal order assumed. Classical deterministic processes in that class are process functions. Baumeler and Wolf described the polytope. Three parties suffice for a violation of a causal inequality. The Lugano function, found by Araújo and Feix and studied by Baumeler and Wolf,

    w(a,b,c) = (not b and c, not c and a, not a and b),

is the standard witness. Each party's input depends on the other two outputs. The dependence graph is a cycle. Every deterministic intervention has exactly one fixed point. Two parties are not enough: the twelve binary two-party process functions are all causally ordered. Tobar and Costa extended the characterisation to any number of parties.

## 5. What the fixed-point clause is doing

The clause is an attempt at the criterion the filters do not give. A map from outputs to inputs is admitted only when every local function, freely chosen, composes with it to give exactly one fixed point. No fixed point is the grandfather case: the intervention has nowhere to land. More than one is the bootstrap: the loop underdetermines its own contents. The freedom is the content of the no-new-physics principle in Baumeler, Costa, Ralph, Wolf and Zych. Any operation possible in an ordinary region remains possible in a region that does not itself contain the closed curve. Consistency is not allowed to forbid the operation. It is allowed only to constrain the global solution.

Dourdent, Leitherer, Boghiu, Simonov, Kunjwal and Acín have since said the same thing without quantifying over interventions. A list of events is the event list of a process function exactly when it is complete and pairwise exclusive. If any two of several questions can be answered jointly, so can all of them. That is a multipartite form of Specker's principle. It is a constraint on the process, not an extra axiom that paradoxical histories have measure zero. Cyclic causation is not the enemy. Cyclic signalling is.

## 6. Reversibility, and the quantization question

Reversibility is not free on the original alphabet. The Lugano function is two-to-one. Of the 256 binary two-party maps, twelve are process functions and none equals its input-output reverse. Baumeler, Costa, Ralph, Wolf and Zych, Theorem 2, restore reversibility by a source, a region with trivial input, and a sink, a region with trivial output. The extended process can be read backwards. The form used here is the permutation unitary

    U |o, e> = |w(o) + e, o>.

The inverse reads the sink as the output string and the source as the difference between the input and w(o). A bijection of a finite set is a unitary. A unitary on a fixed basis is not yet a quantum process. Parties must be able to insert instruments that are not diagonal in that basis. A Hadamard is the test case. If the induced map from source to sink ceases to be trace-preserving, the classical consistency clause has not lifted, and quantum theory needs an extra filter. If it remains trace-preserving for every instrument, the fixed-point clause was already the quantum consistency clause.

Daher Ahmed and Kunjwal conjectured, on 30 September 2026, that every process function purifies to a unitary process. They prove it under mutual exclusivity of control conditions, and under a second sufficient condition, unambiguity, and they note that the bare permutation unitary of the reversible extension may fail to be a valid process. The argument below is that it does not fail. Araújo, Feix, Navascués and Brukner had already written down, in 2017, a purification of the Lugano process by exactly this construction (the standard |x,y> -> |x, y + f(x)> trick, credited there to Baumeler and Wolf); a routed-circuit reconstruction is due to Vanrietvelde, Ormrod, Kristjánsson and Barrett. Baumeler, Gilani and Rashid (2022) proved that the diagonal (dephased) process matrix of every process function is valid, and remarked, without a separate proof for the coherent operator, that the reversible extensions are therefore unitarily extensible. The contribution claimed here is a short general proof for the coherent permutation unitary, for every process function.

## 7. Time symmetry and retrocausality

Price has argued that a time-symmetric ontology for quantum theory should be retrocausal, on the assumption that the quantum state is real. Leifer and Pusey replaced that assumption with lambda-mediation: correlations between a preparation and a later measurement are mediated by the ontic state of the system. No retrocausality, operational time symmetry, and lambda-mediation then imply a timelike Bell factorization, which sequential measurements violate. Maudlin's reply is that the operational time-reverse of an experiment is not always itself an experiment of the same kind. The no-go is conditional.

The dilation in this note is adjacent to that argument, not a solution of it. A process function that violates a causal inequality already has each party's input depending on another party's output. The later setting is an argument of the earlier input. Lambda-mediation, in the strict past-screening sense, fails because of the cycle, not because a retrocausal hidden variable was added by hand. Read forwards, the source is an input and the sink is an output. Read backwards, they exchange roles, and the inverse of the permutation unitary is the reversed process. The objection that the bare Lugano function is not an involution on its own three bits is an objection to refusing the source and the sink. Whether the dependence is the retrocausality Price asked for, or only an operational time-reverse, is a reading of the same operator. The mathematics does not choose the reading. It does remove one cheap reply: one cannot say that the cyclic classical model dies when instruments become unitary.


## 8. What this does not settle

Embeddability is untouched. A unitary process on a finite alphabet is not a solution of Einstein's equation, and it is not a local Hamiltonian flow on a wormhole. The billiard has the wrong multiplicity. Post-selection realises the event list conditional on the post-selection succeeding. The theorem says the list has a unitary dilation. It does not say the dilation is a spacetime.

Purifiability in the sense of open quantum problem 43, whether every extensibly causal process is purifiable, is related but not identical. The theorem puts every process function, including those that violate causal inequalities, inside the unitarily extendible fragment. It does not classify processes that are not deterministic classical functions.

Freedom is not settled. Nothing here decides whether an agent whose output is an argument of an earlier input has a choice. The fixed-point clause says the choice, if made, completes uniquely. It does not say the choice was open. Whether this is an adequate reply to Black depends on whether consistency conditions may rule out interventions, or only rule out histories given the interventions. The note takes the second reading: consistency rules out histories given the interventions, never the interventions themselves (Section 5), and the formalism is built for it.

The combinatorial lemma is finite for any fixed alphabet and is the piece an attacker has to break. The linear algebra after it is row orthogonality. See lean/STATUS.md for exactly what is and is not machine-checked.


## 9. Status of the purification conjecture

Conjecture: a classical process (a point of the Baumeler-Wolf polytope) is purifiable in the sense of Araujo et al. (2017) if and only if it is a mixture of process functions (a "PF blend").

This section is a map of the current status. Labels follow the appendices: **[proved]**, **[certified exact]** (rational certificate, not Lean), **[numerical]**, **[cited]**. Proofs live in the appendices and are not restated here.

**Proved.**
- *Process functions lift* (Section 1, Appendix A). Every process function lifts to a unitary process. The core identity and the validity chain are machine-checked in Lean in finite dimensions (PFUL.induced_unitary; PFUL.Choi.validity_package). Countable alphabets: Appendix F (PFUL.Countable.induced_unitary_l2). Continuous alphabets: open (F.5).
- *Blends lift* (C.1). Every mixture of process functions is purifiable, and convex combinations of purifiable processes are purifiable. This is the "if" half of the conjecture.
- *Classical version* (D.6). A classical process is classically reversibly purifiable iff it is a PF blend. So the conjecture says quantum purifiability adds nothing for classical processes.
- *Two parties* (Appendix G, Theorem G.1). Every bipartite valid classical process, with any finite alphabets, is a blend of causally ordered process functions. So the conjecture holds for two parties, with both sides true. This is known in substance [cited: Oreshkov-Costa-Brukner 2012, Suppl.; Baumann-Brukner 2016].
- *Three parties, a party last* (Theorem H.1). If some party's output influences nothing, the process is a PF blend.
- *Three parties, causally separable* (Theorem H.2). If some party is first and every conditional bipartite process is valid, the process is a PF blend. So every classically causally separable three-party process is a blend of causally ordered process functions, and the conjecture holds on that class trivially.
- *Three parties, a party first in the purification* (Lemma H.6.1, Theorem H.6.2). If some purification of W has a party whose input is prepared from the source alone (operator-level first: V factorises through that party's input), then every conditional bipartite process is valid and purifiable, and W is a PF blend. So a purifiable process outside the hull could only have purifications in which every party's input is influenced by some party output. Lugano has no purification with an operator-first party.
- *Structure of purifications* (D.1, D.2, D.5). The sink records (o, i) orthogonally. Constraints on the fixed source state are vacuous. Validity under quantum-controlled interventions holds for every classical process.

**Certified exact non-purifiable.** E_ex1, and vertex orbits 7 and 50 (one of which contains E_ex1): exact inertia certificates (C.2; code/stochastic/cert). They are not mixtures of process functions, so they agree with the conjecture.

**Settled negatively (routes that provably do not work).**
- *Hidden source label* (D.3/D.4). The single-classical-label strengthening D.3 is false: a causal circuit is an exact counterexample.
- *Fixed-source certificates* (D.8). No certificate that uses only the fixed source sector can rule out purification of any classical process.
- *Marginally-first reduction* (H.5). Purifiability plus "party A's input marginal is output-independent" does not force valid conditionals. The operator-level version does (H.6). An exact counterexample is a 4-term PF blend. So H.2 cannot be extended this way to E_ex1 and orbits 7, 8, 50, even though all of them are marginally first in some party (H.1 numerics).
- *Form-based certificates for orbits 8/10/20* (C.5). Every linear or block-Hermitian combination of the constraint forms tried stalls at lambda_16 ~ +1e-4. Adding the Gram normalisation provably adds nothing. The obstruction is non-convex. The earlier estimate that "about half" of the open orbits are certifiable by the current pipeline is **withdrawn**.
- *Moment relaxation* (Appendix E). The degree-2 relaxation is feasible for E_ex1, so it is weaker than single-form inertia.
- *Single-vector determinantal bound for orbit 8* (H.2 route B) [numerical]. The jointly isotropic cone contains vectors with rank K(u) of about 51-55, so the bound gives only dim <= ~28-32, not < 16.

**Numerical evidence (not proof).**
- *GPU sweep* (C.4). None of the 49 remaining sampled non-deterministic vertex orbits lifted. Best residuals were 12.97-59.35; the same code reaches 1e-16 on Lugano.
- *Isotropic dimension* (C.5). For orbits 8, 10 and 20, constraint-isotropic subspaces appear to exist up to dimension ~10 and fail by 12. A purification needs 16.
- *Facets* (D.7). Facet orbit 82 is violated by E_ex1 and by all 51 sampled non-deterministic vertex orbits.
- *Boundary* (D.8). Along Lugano -> E_ex1, purifiability appears to stop where the PF hull does.
- *Unitary-side hunt* (H.3). Optimising unitaries for purity, classicality and facet violation found no purifiable process outside the hull. From Lugano, facet violation of ~0.01 costs a purity residual of 0.1-2.4.

**Open.**
- The "only if" half for **purifications with no operator-first party**: every party's input is influenced by some party output in V, as in the Lugano-type cyclic lifts. By H.6 this is the only place a purifiable non-blend can live. It contains Lugano-type process functions, their blends, and every candidate counterexample (E_ex1 and all 51 sampled orbits fail first-with-valid-conditionals in every party, so any purification of them has no operator-first party).
- The exact status of **orbits 8, 10, 20** (dim V_W = 82) and **the other 46 sampled open orbits**: numerically non-purifiable, with no exact certificate.
- Deriving any PF-hull facet (for example orbit 82) from purifiability. Any proof must use the purifying unitary on source states orthogonal to the fixed source state (D.2, D.8). That is the non-convex isotropy condition of AFNB Theorem 4.

**Interpretation (philosophical, not a result).** Consistent time loops are the setting: a process function is a loop in which every local choice has exactly one consistent history. The conjecture asks whether chance inside such a loop can be fundamental, or only ignorance about which deterministic loop obtains. If it holds, every reversible quantum loop with classical statistics is a coherent ignorance mixture of deterministic consistent loops. Genuinely chancy loops like E_ex1 would then be classically consistent but not reversibly realisable. Reversibility, not consistency alone, would be the constraint that excludes basic chance from loops. D.4 adds a caveat: the "which-loop" variable can be contextual, so the ignorance reading is about W, not about any single hidden label. H.2 and H.5 sharpen this: wherever a causal order exists, the ignorance reading is automatic. The open question lives entirely in loops without one.

## Appendix A. Unitarity under local unitaries implies validity

**Definitions (AFNB 2017, Sec. 2).** A process with source P, sink F and parties k is an operator W >= 0 on P (x) F (x) prod_k (I_k (x) O_k). For local maps A_k : L(I_k (x) X_k) -> L(O_k (x) Y_k), the induced map is the link product G_A = W * (A_1 (x) ... (x) A_n), a map L(P (x) X) -> L(F (x) Y) with X = (x)_k X_k and Y = (x)_k Y_k. W is *valid* if G_A is CPTP whenever every A_k is CPTP, for all finite-dimensional local ancillas X_k, Y_k. W is *pure* (their Definition 1) if G_A is unitary whenever every A_k is unitary. Their Theorem 2 says W is pure iff W = |U>><<U| for a unitary U. For pure Choi vectors the link product composes operators: if A_k(rho) = V_k rho V_k^dagger, then G_A(rho) = M rho M^dagger, where M is the operator of Section 1.

**Claim.** W = |U>><<U| with U the permutation lift of a process function w is a valid process.

*Step 1 (local unitaries).* By the Theorem of Section 1, G_A is conjugation by a unitary M whenever every A_k is conjugation by a unitary V_k. This holds for any ancilla dimensions with |I_k||X_k| = |O_k||Y_k|. (Machine-checked, both sides, including the dimension count: `PFUL.induced_mul_conjTranspose`, `PFUL.induced_conjTranspose_mul`, `PFUL.induced_unitary`; see lean/STATUS.md.)

*Step 2 (local CPTP maps, via Stinespring).* Let A_k : L(I_k X_k) -> L(O_k Y_k) be CPTP. Stinespring dilation gives an isometry S_k : I_k X_k -> O_k Y_k E_k with A_k(rho) = Tr_{E_k}[S_k rho S_k^dagger]. Pad the input with E'_k of dimension |O_k||Y_k||E_k| and the output with E''_k of dimension |I_k||X_k|. The two sides then have equal dimension, and the isometry psi (x) |0> -> (S_k psi) (x) |0>, defined on the |0>-slice, extends to a unitary V_k : I_k X_k E'_k -> O_k Y_k E_k E''_k by completing orthonormal bases. So A_k(rho) = Tr_{E_k E''_k}[V_k (rho (x) |0><0|_{E'_k}) V_k^dagger]. The ancillas E', E, E'' never enter U, and the link product is multilinear and commutes with appending fixed states and with partial traces on systems it does not contract. Hence

    G_A(rho) = Tr_{E E''}[ M (rho (x) |0><0|_{E'}) M^dagger ],

where M is the operator of Step 1 for the unitaries V_k, with enlarged local ancillas X_k E'_k and Y_k E_k E''_k. Appending a state, a unitary conjugation and a partial trace are each CPTP, so G_A is CPTP.

*Step 3 (shared and entangled ancillas).* An ancilla R that is shared between parties, or entangled with any outside system, is covered by complete positivity. The joint state lives on P X R; G_A (x) id_R is CPTP because G_A is; outputs are normalised states, and every probability that a later measurement on F Y R assigns is non-negative and sums to 1. Pre-shared entanglement between laboratories is the special case in which part of X_j and part of X_k start in an entangled state supplied through the source. It is also covered, because Step 2 already allows arbitrary input states on P (x) X.

*Step 4 (instruments).* Let {A_k^{a_k}} be CP maps summing to a CPTP map A_k. The link product of positive operators (Choi operators) is positive, so each G_a = W * (x)_k A_k^{a_k} is CP. Multilinearity gives sum_a G_a = G_A, which is CPTP by Step 2. Then p(a) = Tr G_a(rho) >= 0 and sum_a p(a) = 1 for every input rho. This is the validity condition of Oreshkov, Costa and Brukner, applied to the process seen by the parties once the source is prepared and the sink discarded. Fixing the source in |0> and tracing the sink yields W_w = sum_o |o><o|_O (x) |w(o)><w(o)|_I, the classical process matrix of w.

So purity gives validity with no further assumption. The only input specific to process functions is Step 1.

**Lean (finite dimensions).** All four steps are machine-checked, standard axioms only.
- *Step 1, isometries:* `PFUL.induced_isometry`. If every local map is an isometry (V_k^dagger V_k = 1, not necessarily square), then M^dagger M = 1. It rests on the column identity with constant row sums (`PFUL.Column.sum_prod_eq_prod`).
- *Step 2, Stinespring:* `PFUL.krausDilP_isometry` and `PFUL.ptrace_krausDil`. Any Kraus family has the isometric dilation V = sum_j K_j (x) |j>, which reproduces the channel. `PFUL.Choi.kraus_of_choi` gives a Kraus family from any PSD Choi matrix (spectral theorem), complete when the map is TP.
- *Step 3, ancillas:* `PFUL.valid_kraus` (with `PFUL.valid` for unitaries). For any joint density matrix of source and ancillas (entangled or shared), the global output and the sink state are density matrices.
- *Step 4, instruments:* `PFUL.valid_instrument`. Outcome-conditioned sink states are PSD and sum to a density matrix, so the probabilities sum to 1.
- *Process-matrix form:* `PFUL.Choi.procMat` defines W = |U>><<U|. `PFUL.Choi.born_eq_trace` shows Tr[W (rho (x) 1_F (x) (x)_k C_k)^T] = Tr[M rho M^dagger]. `PFUL.Choi.bornC_eq_one` gives the AFNB/OCB normalisation = 1 for every source state and all local CPTP Choi matrices.

- *Ancillas, converse, Choi's theorem:* `PFUL.Choi.born_anc_eq_one` and `bornC_anc_eq_one` give the Choi-form normalisation with party ancillas (local maps I_k X_k -> O_k Y_k, ancilla state folded into the source state). `PFUL.Choi.procMat_posSemidef` shows W is PSD. `PFUL.Choi.afnb_iff_density` shows AFNB normalisation is equivalent to the density-matrix condition. `PFUL.Choi.isCP_iff_choi` is Choi's theorem (CP iff PSD Choi matrix), so CP is a theorem rather than a definition.

Bookkeeping: `PFUL.Choi.bornAnc_eq_one` needs no structure on the ancilla types. `PFUL.Choi.bornSplit_eq_one` and `PFUL.Choi.afnb_iff_density_split` use exactly the index layout of `ValidWith`. `PFUL.Choi.validity_package` bundles unitary validity, Kraus-channel validity and AFNB normalisation in one theorem. Not formalised: the Choi form in infinite dimensions, which needs trace-class operators and partial traces on l^2 that Mathlib does not yet have. The unitary layer there is `PFUL.Countable.induced_unitary_l2`.

## Appendix B. Unequal input and output alphabets

Nothing in Section 1 needs |I_k| = |O_k|.

- U : O (x) P -> I (x) F, with P = prod I_k and F = prod O_k, maps |o,e> to |w(o)+e, o>. Both sides have dimension prod |I_k||O_k|, and U is a permutation of basis states, so U is unitary for every w. Only I_k needs a group structure (Z_{|I_k|}); O_k is an arbitrary finite set.
- The exclusivity Lemma and its proof never compare I_k with O_k.
- A party with |I_k| != |O_k| cannot apply a unitary I_k -> O_k. Its most general deterministic operation is a CPTP map, or a unitary with ancillas, I_k X_k -> O_k Y_k with |I_k||X_k| = |O_k||Y_k|. The Theorem is stated in exactly that generality (and so is the Lean theorem, whose local types I k, O k, X k, Y k are independent). The Gram computation gives M M^dagger = 1, and M is square because dim(P X) = prod |I_k||X_k| = prod |O_k||Y_k| = dim(F Y). Appendix A then applies verbatim.

**What holds.** For any finite input and output alphabets, with any sizes, the permutation lift of a process function is a pure and valid process. **What is not covered.** Infinite or continuous alphabets (Baumeler et al. 2019 also treat continuous variables), and lifts built from a different bijection than U.

## Appendix C. Stochastic classical processes

**Question.** Does every logically consistent classical process admit a unitary extension, in the sense of AFNB purifiability? The process may be stochastic, not just a deterministic process function.

**What is known (verified sources).**
- Baumeler and Wolf (NJP 18, 013036 (2016), https://arxiv.org/abs/1507.01714) show the classical processes form a polytope. With two binary parties it has 12 extremal points, all deterministic. With three binary parties it has 710,760 extremal points, of which only 744 are deterministic, i.e. process functions. The rest are "proper mixtures" of logically inconsistent deterministic processes. One explicit example is E_ex1 = (C + C̄)/2, the uniform mixture of the circular identity channel C (x_1 = a_3, x_2 = a_1, x_3 = a_2) and its bitwise negation C̄.
- Araújo, Feix, Navascués and Brukner (Quantum 1, 10 (2017), https://arxiv.org/abs/1611.08535) define purifiability (their Definition 3). Their Theorem 4 is an exact criterion, and Section 5 gives a necessary condition, dim V_W ≥ rank W.
- Baumeler, Gilani and Rashid (Quantum 6, 673 (2022), https://arxiv.org/abs/2104.06234) assert unitary extensibility for process functions only, via reversible embeddings, without a separate proof.
- Daher Ahmed and Kunjwal (https://arxiv.org/abs/2610.00579) conjecture that process functions are purifiable. Tobar and Costa (CQG 37, 205011 (2020), https://arxiv.org/abs/2001.02511) treat reversible deterministic dynamics.
- I found no source that claims to settle purifiability of the non-deterministic extremal points.

**C.1 Proposition (proved).** Every convex mixture of process functions is purifiable.

*Proof.* Let W = sum_j p_j W_{w_j}. Take source P' = C^J ⊗ P and sink F' = C^J ⊗ F, and define U|o, e, j> = |w_j(o) + e>_I |o, j>_F'. With local unitaries inserted, the induced operator is the block sum ⊕_j M_j. Each M_j is unitary by the Theorem of Section 1, so the process is pure. Feed sum_j sqrt(p_j)|j> ⊗ |0> into P'. This is a fixed pure state, equivalently |0> followed by a unitary that is absorbed into U. Then trace out F'. Because the sink keeps a copy of j, the cross terms vanish and the result is sum_j p_j W_{w_j} = W. ∎

The control register must enter through the source and leave through the sink. If it is not handed to the sink, the coherence between branches survives, and the result is no longer the classical mixture. Hence the whole deterministic-extrema polytope of Baumeler and Wolf is purifiable. This covers every two-party classical process with binary inputs and outputs, since there all extremal points are deterministic.

**C.2 E_ex1 is not purifiable (exact certificate).** Scripts are in code/stochastic/.

*Reduction.* In AFNB Theorem 4 the auxiliary sink F' behaves as a party with trivial output. Every term of the projector L_V^⊥ therefore traces out and replaces F'. Write w_i = Σ_k |w_{i,k}>|k>_{F'} and define X_i by X_i |p_k> = sqrt(E_{p_k}) |w_{i,k}>. The conditions become L_3^⊥(X_i Λ X_j^†) = 0 for all i, j, with Λ = diag(1/E) on the support. Here L_3^⊥ is the ordinary three-party projector on 64×64 matrices, and X_0 = W. This takes seconds instead of tens of minutes, and it reproduces the full computation (dim V_W 27 for E_ex1 and 56 for Lugano).

*Certificate.*
- E_ex1 is logically consistent and is a vertex of the three-party binary polytope (active-constraint rank 64 of 64). Hence it is not a mixture of process functions.
- rank W = 16. Exact integer arithmetic (python-flint) gives dim V_W = 27.
- One explicit integer combination of the constraint functionals (code/stochastic/exact.py, cert_phi.npy) gives a sesquilinear form on V_W. Its symmetric part has exact inertia (13 positive, 13 negative, 1 zero), computed by rational congruence elimination.
- The span of w_0, ..., w_15 is a 16-dimensional subspace on which this form must vanish, so it is totally isotropic for the symmetric part. But a totally isotropic subspace has dimension at most 1 + min(13, 13) = 14 < 16. So no purification exists.
- An independent numerical check agrees. A gradient search for purifications reaches residual 8·10^-14 for Lugano (which is purifiable), but stalls at 79.7 for E_ex1.

**C.3 Purifiable set and the conjecture.** The control-register argument of C.1 works for any purifiable processes, not just process functions. So the purifiable classical processes form a convex set containing the hull of the process functions. We conjecture they are exactly that hull:

*Conjecture.* A classical process is purifiable iff it is a mixture of process functions.

*Evidence so far.*
- 40,000 random LP vertices of the three-party binary polytope gave 39,354 deterministic vertices and 646 non-deterministic ones. These fall into 51 orbits under party permutations and local input/output relabellings (code/stochastic/reps.json). Ranks are 15–23.
- AFNB's necessary condition dim V_W ≥ rank W holds for all 51 orbits (nec_partial.json), so on its own it decides nothing. dim V_W ranges from 27 to 256.
- Exact certificates of non-purifiability exist for the 2 orbits with dim V_W = 27, one of which contains E_ex1 (exact2.py, cert_phi_7.npy, cert_phi_50.npy).
- For the other 49 orbits (dim V_W ≥ 82) the random-form isotropy test was inconclusive. The GPU gradient search of C.4 found no purification for any of them (best residual ≥ 12.97). This is numerical evidence only.
- No purifiable non-mixture has been found. That is weak evidence, because the large cases are untested.
- All 1,488 mixtures (q + E_ex1)/2 and (q + 4 E_ex1)/5, with q one of the 744 process functions, lie outside the process-function hull (LP check). They are untested candidates for non-extreme counterexamples.


**C.4 GPU sweep over the 49 open orbits (numerical evidence, not proof).**
- Method: code/stochastic/gpu/gpusearch.py ran on one RTX 3090. For each orbit it made 64 random restarts of batched L-BFGS in float32 on the reduced Theorem 4 residual, then polished in float64.
- Validation: the same code finds Lugano's purification (residual 1.2e-16) and stalls at 79.676 on E_ex1, which is certified non-purifiable.
- Result: no orbit reached the 1e-10 threshold. The best residuals range from 12.97 (orbit 40) to 59.35. Every orbit stalled far from zero.
- Interpretation: this is consistent with the conjecture that none of the 49 non-deterministic vertex orbits is purifiable. But a local search can miss solutions, so it is not a proof. Only orbits 7 and 50 (C.2) have exact certificates.

| orbit | rank | dim V_W | best residual (float64) | restarts |
|---|---|---|---|---|
| 0 | 15 | 124 | 20.12 | 64 |
| 1 | 16 | 176 | 13.03 | 64 |
| 2 | 15 | 156 | 15.62 | 64 |
| 3 | 15 | 156 | 15.49 | 64 |
| 4 | 16 | 128 | 21.93 | 64 |
| 5 | 16 | 160 | 12.98 | 64 |
| 6 | 16 | 144 | 18.48 | 64 |
| 8 | 16 | 82 | 35.84 | 64 |
| 9 | 16 | 112 | 27.06 | 64 |
| 10 | 16 | 82 | 34.75 | 64 |
| 11 | 16 | 128 | 21.72 | 64 |
| 12 | 16 | 112 | 26.91 | 64 |
| 13 | 16 | 196 | 12.97 | 64 |
| 14 | 16 | 144 | 18.49 | 64 |
| 15 | 16 | 168 | 13.02 | 64 |
| 16 | 15 | 156 | 19.57 | 64 |
| 17 | 15 | 164 | 15.82 | 64 |
| 18 | 16 | 160 | 13.02 | 64 |
| 19 | 16 | 160 | 12.97 | 64 |
| 20 | 16 | 82 | 35.32 | 64 |
| 21 | 16 | 128 | 21.73 | 64 |
| 22 | 16 | 164 | 18.44 | 64 |
| 23 | 16 | 172 | 12.99 | 64 |
| 24 | 16 | 112 | 26.78 | 64 |
| 25 | 16 | 136 | 21.76 | 64 |
| 26 | 16 | 128 | 21.88 | 64 |
| 27 | 16 | 144 | 18.5 | 64 |
| 28 | 15 | 124 | 20.12 | 64 |
| 29 | 16 | 144 | 18.51 | 64 |
| 30 | 16 | 168 | 13.02 | 64 |
| 31 | 16 | 160 | 13.02 | 64 |
| 32 | 21 | 160 | 49.61 | 64 |
| 33 | 16 | 164 | 18.46 | 64 |
| 34 | 20 | 174 | 35.72 | 64 |
| 35 | 16 | 160 | 13.02 | 64 |
| 36 | 16 | 160 | 12.97 | 64 |
| 37 | 16 | 160 | 12.98 | 64 |
| 38 | 22 | 176 | 48.56 | 64 |
| 39 | 21 | 146 | 59.35 | 64 |
| 40 | 16 | 196 | 12.97 | 64 |
| 41 | 16 | 204 | 13.01 | 64 |
| 42 | 16 | 172 | 12.99 | 64 |
| 43 | 22 | 224 | 25.58 | 64 |
| 44 | 21 | 160 | 50.3 | 64 |
| 45 | 21 | 174 | 41.12 | 64 |
| 46 | 20 | 166 | 34.6 | 64 |
| 47 | 23 | 248 | 42.74 | 64 |
| 48 | 21 | 172 | 37.9 | 64 |
| 49 | 23 | 256 | 29.02 | 64 |

**C.5 Exact-certificate attempt for the dim V_W = 82 orbits 8, 10, 20 (Oct 21 2026).** Status labels: orbits 7, 50 (and E_ex1) **[certified exact]**; all 49 orbits in the C.4 table **[numerical only]**. No new certificate was obtained.
- Earlier single-form runs (20 time-boxed rounds per orbit, `cert/results_cpu/status.jsonl`) and block forms with k = 2 (`cert/better/NOTES.md`) found no certificate. The best bound was 20.5 > r = 16.
- New numerical probe (`cert/isodim.py`, logs in `cert/better/isodim*.log`; 8 CPU threads, 2 restarts x 600 Adam steps per size). It asks for the largest complex subspace of V_W that is totally isotropic for all constraint forms, ignoring the Gram and fixed-vector conditions. Isotropy loss at dimension 8 / 10 / 12: orbit 8: 1.3e-3 (3.7e-6 after 2,500 steps) / 0.22 / 0.68 (14: 1.46; 16: 2.34); orbit 10: 1.5e-5 / 1.3e-5 / 0.55; orbit 20: 2.0e-6 / 2.6e-4 / 0.53. So isotropic subspaces seem to exist up to dimension about 10 and to fail by 12. That is far below r = 16, which is consistent with non-purifiability, but it is numerical only.
- Why the linear certificate families fail. A Hermitian combination H of the constraint forms certifies only if n+(H) + n0(H) < 16, i.e. n-(H) >= 67 of 82. The searches plateau at lambda_16(H)/||H|| ~ +1e-4. Adding the Gram normalisation C^H G C = tr(W) I does not help: G is PSD, so n+(H + muG) >= n+(H) for mu > 0, and the extended test certifies nothing the plain test cannot. The fixed vector c0 lies in the common radical (NOTES item 3). So the gap between the isotropic dimension (~10) and r (16) is invisible to every linear or block-Hermitian form tried. It is a genuinely nonlinear (non-convex) obstruction. A sound exact certificate would need, e.g., a degree-4 Positivstellensatz showing that some 67-dim subspace of V_W contains no nonzero jointly isotropic vector, or a determinantal argument (rank K(u) > 66 on the jointly isotropic cone). Neither has been set up: an unreduced degree-4 SDP has ~10^4-size blocks, which is beyond this box (8 cores, 15 GB) and far beyond the per-orbit budget. The larger orbits (dim V_W 112-256) face the same obstruction with a larger gap, so the estimate that about half are certifiable by the current pipeline is not supported.

*Proof idea for "only if" (not completed).* A purification U restricted to classical permutation instruments gives a unitary M for every reversible local classical operation. One would like to show that M's action on basis states then decomposes into permutations, giving a deterministic decomposition. We have not proved this. E_ex1 shows the classical consistency of W alone is not enough.

**Answer.** Not every classical process admits a unitary extension: E_ex1 (and one other vertex orbit) provably does not. Mixtures of process functions do. Whether those are the only ones is the open conjecture above.

## Appendix D. Purifications of classical processes: the physics route
Status labels: **[proved]**, **[conjecture]**, **[gap]**. Nothing here proves the conjecture; it is still open.

Setting. A purification of a classical process W (diagonal; equivalently a stochastic map p(i|o) on the joint
classical inputs i and outputs o of the parties) is a unitary V : P (x) O -> F (x) I together with a fixed source
state |psi> in P such that (i) W = Tr_F of the Choi vector of V(|psi> (x) .), and (ii) for every choice of local
operations (unitaries with ancillas) the induced map P (x) ancillas -> F (x) ancillas is unitary (AFNB 2017).
Write  V|psi, o> = sum_i |i> (x) |v_{o,i}>  with  v_{o,i} in F.

**Lemma D.1 [proved].**  <v_{o',i'} | v_{o,i}> = delta_{o o'} delta_{i i'} p(i|o).
Proof. The Choi matrix of the induced channel O -> I is  sum_{o,o'} |o><o'| (x) Tr_F[ V|psi,o><psi,o'|V^dagger ],
whose ((o,i),(o',i')) entry is <v_{o',i'}|v_{o,i}>. W is diagonal with diagonal entries p(i|o). QED.
Consequence: the sink holds a perfect record of the pair (o,i): the normalised vectors f_{o,i} = v_{o,i}/sqrt(p(i|o))
(over the support of W) are orthonormal, so dim F >= |supp W| = rank W = r (the same r as in AFNB Thm 4).
Checked numerically on the source-sink lift of Lugano (code/stochastic/physics/lemma_d1_check.py).

**Lemma D.2 [proved; negative].** Conditions (i)-(ii) restricted to the source state |psi> impose nothing beyond
W being a classical process. For classical deterministic interventions with input copies, o = f(i) (+) a with the
input i copied to a private ancilla, the output for ancilla value a is sum_i |i>_anc (x) sqrt(p(i|f(i)+a)) f_{f(i)+a, i};
by D.1 these are orthogonal for a != a' and have total norm sum_i p(i|f(i)+a) = 1 (logical consistency).
Hence any non-purifiability (e.g. E_ex1, orbits 7 and 50) must come from the action of V on source states
orthogonal to |psi>. Any proof of the conjecture must use those states. This is where proposal (2) breaks down:
the "which-function" label lambda cannot come from a basis of the span of |psi> alone.

**Where proposal (2) fails [gap].** The intended argument: under each intervention the global map is a generalised
permutation conditioned on a source label lambda; expanding |psi> = sum_lambda c_lambda |lambda> gives
W = sum |c_lambda|^2 W_{w_lambda}. Three gaps:
 (a) Unitarity under local unitaries does not obviously make V, restricted to classical party inputs, a generalised
     permutation. D.1 gives orthogonality only for the fixed |psi>, and only after tracing the party wires through W.
 (b) Even when it holds for each intervention f separately, the label lambda may depend on f (no single basis of P
     works for all f). Ruling this out is exactly the noncontextuality-type step that is missing.
 (c) Coherences in |psi> across labels: they vanish from W by D.1, but they constrain V on psi-perp, see (b).

**Conjecture D.3.** If V purifies a classical process, there is an orthonormal basis {lambda} of P such that
V|lambda, o> = phase * |w_lambda(o)> (x) |g_lambda(o)> for functions w_lambda, with g_lambda injective on outputs.
D.3 implies the conjecture: each w_lambda must then be a process function, since V must stay unitary under classical
interventions restricted to the source state |lambda>, and by Baumeler-Wolf that means a unique fixed point.
D.3 holds for our source-sink lifts. It has not been tested on the non-permutation purifications found by the
optimiser (Lugano, App. C); that test is the next step. A counterexample to D.3 that is still a mixture would refute
only D.3, not the conjecture.

### D.4 Conjecture D.3 is false (update, Oct 10 2026) [proved, exact counterexample]

Write G_{i,o} = V_o^dagger (Pi_i (x) 1_F) V_o on P, where V_o|s> = V|s,o>. D.3 is equivalent to: all G_{i,o} are
projectors that commute pairwise (their common eigenbasis is the label basis lambda). Counterexample: a causally
ordered circuit (code/stochastic/physics/d3_counterexample.py). Party A has trivial input and output oA. The source is
P = m (x) a. Apply H^{oA} to m, CNOT m -> a, send m to B's input, and route (oA, oB, a) to the sink. V is a
permutation-and-Hadamard circuit of unitaries in a fixed causal order, so it is a valid unitary process. With
psi = |00> the process is classical: p(iB|oA=0) = delta_{iB,0} and p(iB|oA=1) = 1/2. Lemma D.1 holds: W is diagonal.
W is a mixture of process functions (w_lambda(oA) = lambda*oA). But the G's are Z-projectors for oA=0 and
X-projectors for oA=1. They do not commute (commutator norm 1/2), so no source basis works. Restricting to psi does
not help either: psi = |00> is an eigenvector of the oA=0 projectors only.

Consequence. Gap (b) is real. Even for causal processes, the "which-function" randomness is generated contextually,
by measuring the quantum source in a basis that depends on earlier outputs. So no argument that extracts a single
classical label from the source can work, and unitarity under all local unitaries does not force one. The mixture
conclusion still holds here for a different reason: every causally ordered classical process is a mixture of causal
deterministic ones. A proof of "purifiable => mixture of process functions" therefore has to show directly that
W lies in conv(PF), for example that purifiability implies every facet inequality of the PF polytope. It cannot go
through a source-label decomposition. Status: the conjecture is open; D.3 is refuted; no counterexample to the
conjecture itself.

### D.5 The hull route (Oct 10 2026)

**Proposition D.5 [proved]: validity under quantum-controlled interventions is automatic, so it cannot be the
criterion.** Let W be any classical process, including E_ex1 and all 49 open orbits. Let the parties apply arbitrary
local instruments, coherently controlled by a shared ancilla that may be entangled across parties. Then the
probabilities are normalised. Reason: W is diagonal, so it dephases every party's input and output. The effective
intervention is then a classical joint behaviour q(o|i) produced from a shared quantum state by local operations, so
q is non-signalling. Every non-signalling behaviour is an affine (not necessarily convex) combination of local
deterministic ones. The normalisation sum_{i,o} p(i|o) q(o|i) is affine in q and equals 1 on every local
deterministic q (logical consistency), so it equals 1 for all such q. Positivity is termwise. So the proposed test
"valid under quantum-controlled interventions" holds for every classical process. It cannot separate E_ex1 from PF
mixtures, and step (3) of the plan is moot. Purifiability is strictly stronger only because of its unitarity
(reversibility) requirement.

**Proposition D.6 [proved, sketch]: classical-reversible purifiability <=> mixture of PFs.** Call W
classically purifiable if it is the marginal, for a random source value lambda, of a classical reversible process: a
bijection (lambda, o) -> (i, sink) that stays a bijection P -> F under every deterministic local intervention.
For a fixed lambda this is a deterministic process. Bijectivity of the composite map under every intervention f
forces exactly one consistent execution: zero leaves the source value with no image, and two collide by counting.
So each w_lambda is a process function (Baumeler-Wolf 2016), and W = sum_lambda p(lambda) W_{w_lambda}. The converse
is the source-sink construction with a random source. Hence **the conjecture is equivalent to: a classical process
that is quantum-purifiable is already classically purifiable.** D.4 shows the quantum purification itself need not be
classical (its labels are contextual), so this has to be argued at the level of W.

**Facets of the PF hull [computation].** The 744 process functions (3 parties, binary) span a 37-dimensional affine
space. Facet enumeration results are recorded below. Each facet that some open orbit violates is a candidate
inequality that purifiability would have to imply.
Full facet enumeration was not done: pycddlib does not build on the box, and 744 vertices in dimension 37 may have
very many facets. Instead, sep.py finds by LP a separating inequality of the PF hull (box-normalised, |f| <= 1):
E_ex1 and orbit 7 violate one by 6.0, orbit 8 by 4.0, and a PF mixture by 0, as expected. These inequalities are not
reduced modulo the affine hull or by symmetry, so their supports carry no meaning yet. **No inequality has been
derived from purifiability. The conjecture remains open.** Next steps: enumerate facets with lrs/normaliz or by
symmetry-adapted LP, then try to derive one facet class from Theorem 4 (isotropy) together with Lemma D.1.

### D.7 Facets of the PF hull: partial (Oct 10 2026)

Tools. lrslib 7.3 builds from source with gcc (no make, no GMP on the box; hybrid 64/128-bit plus built-in MP
arithmetic). normaliz and PANDA were not installed: there is no make/cmake, conda or sudo on the box. The full
enumeration with lrs (744 vertices in the 37-dim span, `facets/pf.ext`) produced no output in 5 minutes, not even
from `estimates`, because the input is highly degenerate. **No facet count or runtime estimate yet.** A double
description or symmetry-exploiting code (normaliz, PANDA with the 384-element symmetry group) on a rented
multi-core CPU is the natural next step; its cost is unknown until a short benchmark is run.

Facets found by polar LP (`facets/facetlp.py`). Each LP optimum was checked to be a facet: its tight PFs have affine
rank 36. Facets are classified up to the 384 symmetries (party permutations and input/output relabelings; all 384
preserve the PF set). Over E_ex1 and the 51 sampled non-deterministic vertex orbits, the optimal separating facets
fall into **8 classes**. Class 0 (418 tight PFs) is violated by E_ex1 and 24 orbits, including orbit 8. Class 2 (418)
covers orbits 7, 50 and 15 others; classes 1, 3-7 cover the rest. The class-0 facet, written with joint inputs i and
outputs o (bits of parties A, B, C):

    p(000|000) <= p(000|001) + p(010|001) + p(000|100) + p(010|110) + p(011|111)

E_ex1 gives 1/2 > 0. Combinatorial content for a process function w: if w(000) = 000, then w(001) is 000 or 010,
or w(100) = 000, or w(110) = 010, or w(111) = 011.

**Derivation from purifiability: not achieved.** A natural attempt: use Lemma D.1 to read p(i|o) as squared norms of
orthogonal sink vectors, then try to show the class-0 inequality follows from unitarity under suitable superpositions
of the five interventions involved. This has not been carried through and is not claimed.

#### D.7 update: complete facet list (normaliz, Oct 10 2026)

Run: normaliz 3.8.9 (`-c -x=32`) on a rented 32-core vast.ai CPU instance, about 1.9 h, about $0.27 in total; the
instance was then destroyed. Input `facets/pf.in` (744 PFs in 37 independent coordinates of p(i|o); all test points
lie in the same affine span). Output `facets/pf.out.gz`.

**The 3-party binary PF hull has exactly 29,344 facets, in 93 orbits** under the 384-element symmetry group
(`facets/classify.py`, `classes_full.json`). Orbit sizes: 384 (66 orbits), 192 (17), 128 (2), 96 (5), 64 (3).
The 8 LP classes of D.7 are all among them: LP classes 0, 1, 2 are full orbits 82, 83, 84 (418 tight PFs);
classes 3-6 are orbits 42, 38, 37, 41 (238); class 7 is orbit 91 (436).

Violations. E_ex1 violates 24 of the 93 facet orbits, orbit 7 violates 53, orbit 8 violates 41, and every test point
violates at least one. **Facet orbit 82, the class-0 inequality of D.7
p(000|000) <= p(000|001)+p(010|001)+p(000|100)+p(010|110)+p(011|111), is violated by E_ex1 and by all 51 sampled
non-deterministic vertex orbits** (by some member of the facet's orbit). So this single inequality class separates
every sampled non-deterministic vertex from the PF hull. Proving it from purifiability is the natural next target.
Status: facet list exact (normaliz); the derivation from purifiability is open.

### D.8 Toward deriving facet orbit 82 from purifiability (Oct 10 2026): not proved

Sanity checks. Lugano and all PF mixtures satisfy every PF-hull facet, by construction. E_ex1 violates orbit 82
(D.7).

**Proposition D.8 [proved, negative]: no certificate built from the fixed source state alone can work.**
The proposal was an SDP over Gram matrices of sink vectors, with the source in |psi> and parties applying arbitrary
local unitaries (with ancillas, e.g. Hadamard superpositions of deterministic interventions). All such Gram data is a
linear function of W. Inner products between outputs for ancilla inputs a, a' are Tr[W (M_a (x) M_a'^dagger ...)].
Unitarity on the psi-sector (orthonormal outputs for orthonormal ancilla inputs) follows from validity of W under the
local operations that prepare the ancilla in a, a', (a+a')/sqrt2 and (a+ia')/sqrt2. By D.5 every classical process,
including E_ex1, is valid under all such operations. So these constraints are satisfiable by E_ex1, and any SDP over
psi-sector Gram data is feasible for it: no dual certificate exists. (This strengthens D.2 from classical to
arbitrary local interventions.) Any derivation of the facet must use V on source states orthogonal to psi. In AFNB
Thm 4 terms, that is the non-convex isotropic-subspace condition, the same obstruction met in the certificate work
(App. C). **The facet has not been derived; no certificate was found.**

Numerical boundary test (`physics/boundary.py`, `boundary.json`). On x_t = (1-t) Lugano + t E_ex1, the PF hull is
left at t_h ~ 2e-7: Lugano is a vertex and this direction exits the hull at once. The full purification search
(gpusearch, float64, 8 restarts) finds no purification at t = 0.02 (best residual 52.2; rank 19, dim V_W 88) or at
t = 0.2 (60.1); the same code reaches about 1e-13 on Lugano itself. This is consistent with the conjecture, since the
purifiable set appears to end where the PF hull does along this line. It is numerical evidence, not a proof.
Generalisation to other facet orbits: not attempted, since no certificate exists to generalise.

### D.9 Facet orbit 82 from purifiability: reductions and a negative result (Oct 22 2026): not proved

Status labels: **[proved]**, **[proved, exact]** (rational arithmetic), **[failed]**. The derivation of facet orbit 82 from purifiability is still open. Code: code/stochastic/physics/d9/ (f82_exact.py, log f82_exact.log).

**D.9.1 The facet orbit, exactly [proved, exact].** The images of p(000|000) <= p(000|001)+p(010|001)+p(000|100)+p(010|110)+p(011|111) under the 384 symmetries are 384 distinct inequalities. In exact rationals: every one of the 744 PFs satisfies all 384 (maximum value 0), with 418 tight PFs per member. E_ex1 violates 48 members, each by 1/2. Every one of the 51 sampled vertex orbits (reps.json, entries rounded to the exact rationals they represent) violates at least one member. The maximum violation is 1/2, except orbits 32, 34, 38, 39 and 43-49, where it is 1/3. Members violated per orbit range from 1 (orbits 2, 3, 13, 19, 37, 40) to 48 (orbit 50). This turns the D.7 numerical claim into an exact one.

**D.9.2 Where facet 82 is already proved [proved].** Facet 82 holds for every purifiable W that has a purification with an operator-first party (H.6.2), or that has a W-level last party (H.1). In both cases W is a PF blend. So a purifiable W violating facet 82 has only purifications in which every party's input has a parent among the party outputs (H.6). This adds nothing to H.6; it only states the facet consequence.

**D.9.3 Averaging the validity identity gives nothing [proved, negative].** The idea was to average the purity identity M M^dag = 1 over Haar (or 2-design) local unitaries, which gives linear and quadratic constraints, and then derive facet 82 by a small SOS in the 37 diagonal variables. This cannot work for constraints read on the fixed source state psi. Each such constraint is a polynomial in the numbers <psi, a|M^dag ... M|psi, a'> for local operations and ancilla states, possibly averaged. By D.8 these numbers are linear in W. Their values are forced by validity of W under local operations with ancillas, and by D.5 every valid classical W, E_ex1 included, is valid under all of them. Each such identity is therefore satisfied by E_ex1, and so is any Haar or design average of products of these numbers. No degree-2 (or any degree) certificate in the diagonal variables alone can be built from them. Constraints that use V on psi-perp involve the off-diagonal blocks of the full Choi vector on P and F. Eliminating those blocks is the AFNB Thm. 4 isotropy problem, which is non-convex (C.5). Also, the purifiable set is convex (C.3). So any diagonal-only necessary condition that implies facet 82 implies it only through its supporting hyperplanes, and a quadratic inequality has no advantage over a linear one. The proposed numerical test (idea 4) is moot for psi-sector constraints. **[failed: idea (3) is vacuous in its psi-sector form]**

**D.9.4 Where the attempt stopped.**
- D.8's failure point is unchanged. A derivation must use V on source states orthogonal to psi, where the only known exact handle is single-form inertia (C.2). That handle fails for every orbit with dim V_W >= 82 (C.5).
- The cyclic route (H.6, idea 2) needs a structure theorem for unitary processes whose BLO causal graph has every party influenced, for example "each input is a routed function of the other outputs and the source". BLO 2021 leave cyclic structure open, and I found no such theorem. No constraint on the diagonal was derived from cyclicity. The cyclic purification search (code/stochastic/cyclic/, future H.7) is separate work and was not touched.
- No new exact non-purifiability certificate was obtained. Status: facet 82 is proved for the purifiable W covered by H.1 and H.6. For the rest it is open.

## Appendix E. Symmetry-reduced moment relaxation (negative result)

**Stabilisers** in the 384-element group of party permutations and input/output relabelings: E_ex1 and orbit 50: 48; orbit 7: 16; orbits 8 and 20: 8; Lugano: 6; orbits 10 and 46: 4; 11 orbits: 2; 34 orbits: 1. Symmetry helps most where certificates already exist, and not at all for most open orbits.

**Relaxation.** Variables P (m x m) and Y (m^2 x m^2), Hermitian, with Y standing for P (x) P and F the swap. A rank-r projector onto a totally isotropic subspace satisfies Y >= 0, 0 <= P <= I, tr P = r, Tr_2 Y = rP, Tr_2(YF) = P (from P^2 = P), P (x) I - Y >= 0 and Tr_1[(Q_t (x) 1)YF] = P Q_t P = 0 for every form. So infeasibility would certify non-purifiability, for complex subspaces. The constraints are covariant under the stabiliser, so symmetry reduction would be legitimate.

**Result: too weak.** For E_ex1 (m = 27, r = 16) the unreduced problem is small enough to solve directly by cyclic projections (code/stochastic/rep/pocs.py). The solver was checked on controls: it reaches feasibility at r = 1, 2, 4, and a 4-dim isotropic subspace exists numerically. At r = 16 the relaxation is feasible with strict margins: min eig Y = 0.13, eig P in [0.58, 0.63], min eig of P (x) I - Y = 0.019. P is close to (16/27)·I. E_ex1 is non-purifiable and certified by single-form inertia, so this relaxation is strictly weaker than the inertia test. Symmetry-reducing it is pointless. Stronger convex certificates would need higher moment levels or must encode rank.

## Appendix F. Infinite and continuous alphabets (draft)

**Literature (verified).** Giacomini, Castro-Ruiz and Brukner extend the process-matrix framework to continuous-variable systems. Naive infinite-dimensional process matrices are singular, and they use a phase-space (Wigner) representation instead (New J. Phys. 18, 113026 (2016); https://arxiv.org/abs/1510.06345). The Baumeler-Wolf polytope work is for finite alphabets (https://arxiv.org/abs/1507.01714). The fixed-point characterisation of logical consistency (Baumeler and Wolf, https://arxiv.org/abs/1511.05444) and the 2025 flow-of-causal-structures paper (Phys. Rev. Research, doi:10.1103/jsmm-tq72) work with discrete alphabets. We found no treatment of process functions on infinite alphabets, or of their unitary lifts.

**Setting.** Finitely many parties. Each input alphabet I_k is a countable set carrying a group structure (e.g. Z), and the outputs O_k are countable. Hilbert spaces are l^2 of these sets. A process function has a unique fixed point for every choice of local functions, exactly as before.

**F.1 [proved] The lift is unitary.** U|o,e> = |w(o)+e, o> is a bijection of basis states, with inverse (i,f) -> (f, i - w(f)). So it is a unitary on l^2, in any cardinality.

**F.2 [proved] Matrix elements and rows.** Let V_k : I_k (x) X_k -> O_k (x) Y_k be unitaries, with X_k, Y_k countable ancilla bases (they may be shared or entangled across parties; unitarity is a property of the operator, so product bases suffice). Closing the loop with U gives matrix elements whose defining sum over (o, i) has exactly one nonzero term. So no convergence question arises:
<f,y|M|e,x> = <f,y| V |w(f)+e, x>,   with V = (x)_k V_k.
Define u_{f,y} := sum_{e,x} conj(<f,y|M|e,x>) |e,x> = T_{-w(f)} V^dagger |f,y>, where T_a translates the source register by a. Each u_{f,y} is a unit vector. For f != f', the exclusivity lemma gives a party k with f_k != f'_k and w_k(f) = w_k(f'), so <u_{f,y}|u_{f',y'}> has the factor <f_k,y_k|f'_k,y'_k> = 0. For f = f' and y != y' the factor is <y|y'> = 0. Hence {u_{f,y}} is an orthonormal set, and M^dagger, defined on the basis by |f,y> -> u_{f,y}, extends to an isometry. So M is a bounded operator with M M^dagger = 1. Only basis vectors and the standard extension of an isometry from an orthonormal basis are used; no strong limits are needed.

The exclusivity lemma holds for any cardinality. If s != s' and no such k existed, then w_k(s) != w_k(s') whenever s_k != s'_k. Choose local functions with f_k(w_k(s)) = s_k and f_k(w_k(s')) = s'_k (and f_k constant if s_k = s'_k). Both s and s' are then fixed points, a contradiction. Only two values of each f_k are prescribed.

**F.3 [proved] M is unitary (the column side, F.4 in the earlier draft).** An orthonormal set {u_{f,y}} is complete iff sum_{f,y} |<e,x|u_{f,y}>|^2 = 1 for every basis vector |e,x> (Parseval). Now
sum_{f,y} |<f,y|V|w(f)+e,x>|^2 = sum_f prod_k q_k(f_k | w_k(f)),  where q_k(o|i) := sum_{y_k} |<o,y_k|V_k|i+e_k, x_k>|^2.
For each i, q_k(.|i) is a probability distribution on O_k, because V_k is unitary (its columns are unit vectors). Draw the local functions f_k(i) independently, with law q_k(.|i), for every k and i: a countable product of probability spaces. For a fixed o, the event {f_k(w_k(o)) = o_k for all k} has probability prod_k q_k(o_k|w_k(o)). By Tonelli,
sum_o prod_k q_k(o_k|w_k(o)) = E[ number of fixed points of o -> f(w(o)) ] = 1,
since every deterministic choice of local functions has exactly one fixed point. Hence each column has norm 1, the set is complete, and M^dagger M = 1. **Every process function on countable alphabets (inputs carrying a group structure) lifts to a unitary process: U is unitary and so is every induced map.** This argument also gives a dimension-free proof in the finite case. *Machine-checked in Lean for finite alphabets:* `PFUL.Column.sum_prod_eq_one` (the fixed-point averaging identity, over any commutative ring), `PFUL.induced_colnorm` (unit columns), and `PFUL.induced_conjTranspose_mul_of_colnorm` (Mᴴ M = 1 from orthonormal rows plus unit columns, with no dimension count). Standard axioms only. For countable alphabets, the column identity and unit column norms are machine-checked too: `PFUL.Countable.tsum_prod_eq_one` (ℝ≥0∞ sums, via the product measure `Measure.infinitePi`; inputs of any cardinality) and `PFUL.Countable.induced_colnorm`. Row orthonormality (`PFUL.Countable.induced_rows`, using the factorisation lemma `PFUL.Countable.hasSum_pi_prod`) and the assembly are machine-checked as well: `PFUL.Countable.induced_unitary_l2` gives a linear isometric equivalence between the ℓ² spaces whose matrix is M. So in Lean M is unitary for countable alphabets. Exclusivity gives orthogonal rows, and logical consistency under stochastic interventions gives unit columns.

The earlier draft's special cases (permutation interventions; causally ordered w) are now corollaries. The earlier remark that two-party process functions are causal still holds for any cardinality, by the two-fixed-point argument: first w_k is independent of o_k, then w_A and w_B cannot both be non-constant. That remark is no longer needed. No counterexample search is needed either, because F.3 rules out proper co-isometries.

**F.5 Continuous alphabets [partly definitional].** Take I_k a locally compact abelian group with Haar measure (R, U(1)), and w measurable. Then U is a measure-preserving bijection of O x P, so it is unitary on L^2 (F.1 carries over). The induced map, however, involves pointwise evaluation <f|V T_{w(f)}. That is undefined for general unitaries on L^2, so "unitary under all local unitaries" first needs a definition, for instance via the phase-space approach of Giacomini et al. For measure-preserving local bijections the induced map is the bijection e -> f(e). It is measure-preserving in the causal case (Fubini), but this is open in the non-causal case.

**Status.** Proved (paper and Lean, finite and countable), for countable alphabets with a group structure on the inputs and finitely many parties: the lift is unitary under all local unitaries with ancillas (F.1-F.3). Open: continuous alphabets, where the induced map first needs a definition (F.5). The proof of F.3 suggests the natural definition, via the kernel <f|V|w(f)+e> with Haar measure, and the same probabilistic argument would then need the measurable-selection version of "exactly one fixed point".

## Appendix G. Two parties: the conjecture holds, trivially (Oct 21 2026)

**Theorem G.1 [proved].** Let p(a,b|x,y) be a valid classical process on two parties A, B, with finite alphabets of any sizes: a, b are the inputs and x, y the outputs. Valid means p >= 0 and sum_{a,b} p(a,b|f(a),g(b)) = 1 for all functions f, g. Then p is a convex combination of deterministic causally ordered process functions. Each of these has one of two forms: a = a0 constant and b = h(x), or b = b0 constant and a = h(y).

**Corollary G.2 [proved].** For two parties, the purification conjecture of Section 9 holds. Both sides are true for every valid classical process. Every such process is a mixture of process functions (G.1), so it is purifiable (C.1). Also, every bipartite process function is causally ordered: a 0/1 point that is a convex combination of 0/1 points equals one of them. So the two-party case says nothing about the open multipartite question. The separation between "classically consistent" and "reversibly realisable" starts at three parties, where E_ex1 lives.

*Proof of G.1.* Write every function of (a,b,x,y) as a sum of components p_S, one for each subset S of {a,b,x,y}. The component p_S depends only on the variables in S, and its sum over any one variable in S is zero. (These are the products of "average" and "traceless" projections.)

*Step 1 (linear constraints).* Validity for deterministic f, g gives the same normalisation for stochastic local maps sigma(x|a), tau(y|b), by linearity. The quantity sum p sigma tau is affine in each argument, so its derivatives along traceless directions vanish.
- Second order: sum p delta(x|a) eps(y|b) = 0 whenever sum_x delta = 0 and sum_y eps = 0. Such products span all functions that are traceless in x and in y, so p_S = 0 whenever S contains both x and y.
- First order with tau uniform: sum p delta(x|a) = 0 for every delta with sum_x delta = 0. Summing over b and y keeps only S with b, y not in S, so p_{x} = p_{ax} = 0. Symmetrically, p_{y} = p_{by} = 0.

What survives is p = c + s + t, with c = p_∅ + p_a + p_b + p_ab, s = p_bx + p_abx and t = p_ay + p_aby. Here c(a,b) is the average of p over (x,y), so it is a probability distribution. Also sum_x s = sum_b s = 0 and sum_y t = sum_a t = 0. This is the diagonal case of the Oreshkov-Costa-Brukner term structure.

*Step 2 (positive split).* Let m1(a,b) = -min_x s(a,b,x) and m2(a,b) = -min_y t(a,b,y). Both are >= 0 because s and t have mean zero. Evaluating p >= 0 at the minimising x and y gives c >= m1 + m2. Choose c1 >= m1 and c2 >= m2 with c1 + c2 = c, and put U = c1 + s and V = c2 + t. Then U, V >= 0 and p = U + V. Since sum_b s = 0, U(a,b|x) has total mass q = sum c1 for every x, and its A-marginal sum_b c1(a,b) does not depend on x. So U/q = r(a) r(b|a,x) is a classical A-before-B process. By the same argument, V/(1-q) is a B-before-A process.

*Step 3 (deterministic decomposition).* r(a) r(b|a,x) = sum_{a0} r(a0) delta_{a,a0} sum_h prod_x r(h(x)|a0,x) delta_{b,h(x)}, where h ranges over the functions X -> B. Each term is a = a0, b = h(x). Under any interventions it has exactly one consistent history, a0, f(a0), h(f(a0)), so it is a process function. The same holds for the B-before-A part. ∎

**Literature [cited].**
- Oreshkov, Costa and Brukner (Nat. Commun. 3, 1092 (2012), Supplementary) prove that the bipartite process matrices diagonal in fixed bases are causally separable. Their proof is the quantum version of Step 2.
- Baumann and Brukner (arXiv:1601.06620) extend this to inputs diagonal and outputs arbitrary. They note that it fails for three parties (Baumeler, Feix and Wolf, PRA 90, 042106 (2014)).
- For two binary parties, Baumeler and Wolf (2016) report that all 12 vertices of the classical polytope are deterministic (Appendix C). G.1 is the general-alphabet version.

G.1 itself is therefore known in substance. Combining it with C.1 to settle the two-party purification statement is immediate. I did not find a source that states the purification version explicitly. Steps 1-3 are included so that the note is self-contained. Suggested wording for Section 9: "For two parties the conjecture holds, because every bipartite classical process is causally separable [OCB 2012, Suppl.; see also Baumann-Brukner 2016] and hence a mixture of causally ordered process functions (Appendix G)."

**Numerical check [numerical].** The script is code/stochastic/bipartite/vertices.py. For each alphabet size it samples LP vertices of the bipartite classical-process polytope (300 random objectives) and checks that each vertex is 0/1. It also checks 50 averages of 4 random vertices for membership in conv(PF) by LP.

| (|A_in|,|A_out|,|B_in|,|B_out|) | process functions | distinct vertices found | non-deterministic | outside conv(PF) |
|---|---|---|---|---|
| (2,2,2,2) | 12 | 12 | 0 | 0/50 |
| (3,2,2,2) | 24 | 24 | 0 | 0/50 |
| (2,3,2,2) | 20 | 20 | 0 | 0/50 |
| (3,3,2,2) | 36 | 36 | 0 | 0/50 |
| (2,2,3,3) | 36 | 36 | 0 | 0/50 |
| (3,2,3,2) | 45 | 45 | 0 | 0/50 |

For larger alphabets, code/stochastic/bipartite/vertices_only.py does the vertex test alone (enumerating process functions is too costly there):

| (|A_in|,|A_out|,|B_in|,|B_out|) | LPs | distinct vertices found | non-deterministic |
|---|---|---|---|
| (3,3,3,3) | 500 | 146 | 0 |
| (4,2,4,2) | 300 | 100 | 0 |
| (2,4,2,4) | 300 | 60 | 0 |

In every case the vertices found are exactly the process functions, as G.1 predicts. The (2,2,2,2) count of 12 matches Baumeler-Wolf.

## Appendix H. Three parties: structural reductions, a determinantal probe, and a unitary-side search (Oct 21 2026)

Status labels: **[proved]**, **[numerical]**, **[cited]**, **[failed]**. The three-party conjecture remains open. Code: code/stochastic/structural/.

Notation. Inputs a, b, c; outputs x, y, z; a classical process p(a,b,c|x,y,z) >= 0 with sum_{a,b,c} p(a,b,c|f(a),g(b),h(c)) = 1 for all local functions f, g, h. Any finite alphabets unless stated.

### H.1 Route A: classes that reduce to Appendix G

**Definitions.** Party A is *last* if p does not depend on x. A is *marginally first* if p(a|x,y,z) := sum_{b,c} p does not depend on (x,y,z). A is *first with valid conditionals* if, in addition, for every a with p(a) > 0 and every x, the conditional q_{a,x}(b,c|y,z) = p(a,b,c|x,y,z)/p(a) is a valid bipartite classical process. A process is *classically causally separable* if it is a convex combination of processes, each with some party first with valid conditionals. This is the diagonal (classical) analogue of the recursive definition of Wechs, Abbott and Branciard (NJP 21, 013027 (2019), Def. 5) and of Oreshkov-Giarmatzi's extensible causal separability [cited; the definitions were checked against arXiv:1807.10557. I have not checked that the classical specialisation with extensions reduces exactly to the one used here, so it is offered as an analogue].

**Theorem H.1 [proved].** If some party is last, p is a mixture of process functions in which that party is last.

*Proof.* Say A is last. The B,C marginal r(b,c|y,z) = sum_a p is a valid bipartite process (take f arbitrary). By G.1, r = sum_l mu_l delta[(b,c) = w_l(y,z)], with each w_l a causally ordered bipartite process function. Put t(a|b,c,y,z) = p/r where r > 0, and any distribution elsewhere. Expand t as a product mixture of deterministic functions alpha(b,c,y,z), with weight prod_{args} t(alpha(args)|args). Then p = sum_{l,alpha} mu_l nu(alpha) delta[(b,c) = w_l(y,z)] delta[a = alpha(b,c,y,z)]. Each term is a process function: given g, h, the B,C part has one fixed point, and then a is determined. ∎

**Theorem H.2 [proved].** If some party is first with valid conditionals, p is a mixture of process functions in which that party is first. Hence every classically causally separable 3-party process is a mixture of causally ordered process functions, and the purification conjecture holds on that class (both sides true, via C.1).

*Proof.* Say A is first. By G.1, q_{a,x} = sum_l mu(l|a,x) W_l, with W_l ranging over the finitely many bipartite causally ordered process functions. Then p = sum_{a0} p(a0) sum_{lambda: X -> L} prod_x mu(lambda(x)|a0,x) delta[a = a0] W_{lambda(x)}(b,c|y,z). The term (a0, lambda) has a = a0, and then (b,c) given by the process function W_{lambda(x)}. Under interventions f, g, h, x = f(a0) is fixed, and W_{lambda(x)} has exactly one fixed point, so the term is a process function. ∎ The result extends to N parties by induction when the definition is recursive (the conditional (N-1)-party process is required to be separable). For N = 3, G.1 makes the bipartite recursion automatic.

**Marginally first is not enough [proved].** E_ex1 = (C + C̄)/2 is marginally first in every party: party 1's input is o_3 or its negation with probability 1/2 each, so it is uniform whatever the outputs are. Yet it is not a mixture of process functions (C.2). The conditional for a_1 is a3 = o2 + [o3 != a1], a2 = o1 + [o3 != a1] (mod 2). With the intervention o3 = h(a3), this has 0 or 2 fixed points, so it is invalid. The validity of conditionals carries the whole content.

**Numerics [numerical]** (classes.py, classes.json; 3 binary parties, 300 random LP objectives on each sub-polytope; every distinct vertex was tested for 0/1 and for membership in conv(744 PFs)):

| sub-polytope | distinct vertices | non-deterministic | outside conv(PF) |
|---|---|---|---|
| A last | 157 | 0 | 0 |
| A first with valid conditionals | 187 | 0 | 0 |
| A marginally first | 208 | 39 | 11 |

The first two rows agree with H.1 and H.2. Of E_ex1 and the 51 non-deterministic vertex orbits, none is last or first-with-valid-conditionals in any party. 19 of them are marginally first in at least one party, including E_ex1, orbits 7 and 50 (all three certified non-purifiable), and orbit 8 (marginally first in parties 1 and 2).

**Where Lugano sits [cited/proved].** The Lugano (Araújo-Feix / Baumeler-Wolf) process function violates a causal inequality (Baumeler, Feix, Wolf, PRA 90, 042106 (2014), arXiv:1403.7333) [cited]. So it is not causally separable. Directly: each input depends non-trivially on outputs of both other parties, so no party is marginally first, and every output is used, so no party is last [proved]. It lies outside every reducible class, but it is a process function. The interesting class is exactly conv(PF) minus the causally separable processes, together with the candidate non-hull processes, and the reductions say nothing about either.

**Does purifiability add anything here?** On the classes of H.1 and H.2, no: every valid process is already a PF mixture. The natural next statement would be "purifiable and marginally first imply valid conditionals". It would settle the conjecture for the 19 marginally-first orbits, including orbit 8. It is open [not proved]. D.2 and D.8 show it cannot follow from the source sector alone.

### H.2 Route B: a determinantal bound for orbit 8 [failed, numerical]

Idea. If S is a jointly isotropic subspace (AFNB Thm 4, reduced as in C.2) and u is in S, then S lies in ker K(u), where K(u)_{t,b} = Q_t(u, e_b) runs over the 196 linearly independent constraint forms of orbit 8 (m = dim V_W = 82). So dim S <= dim R + (82 - rank K(u)) for any isotropic u outside the common radical R (dim R = 1, spanned by c0). An exact proof would need rank K(u) >= 67 on the whole isotropic cone outside R. That is one determinantal variety (67-minors) with no real point on the cone, which can be checked algebraically in principle.

Probe (detprobe.py). Generic near-isotropic u (residual ~1e-7 to 1e-6) have numerical rank 81. But minimising the tail singular values of K(u) along the cone gives points whose spectrum drops from 1.6e-2 (sigma_50) to 3.4e-4 (sigma_55) and stays there down to sigma_66, with isotropy residual 2.5e-7. So, numerically, the cone contains u with rank K(u) of about 51-55. The single-vector bound then gives only dim S <= ~28-32, not < 16. The determinantal route with one vector cannot work for orbit 8. A flag version (rank conditions on pairs u, v in S) would be needed, and it is a much larger variety. Not attempted. Gröbner bases on a symmetric ansatz were not attempted, because the stabiliser of orbit 8 has order 8 (App. E), too small to reduce the 82 complex unknowns per basis vector to a tractable size. **No exact proof for orbit 8.**

### H.3 Route C: counterexample hunt from the unitary side [numerical, negative]

Parametrisation (hunt.py). U = U0 exp(iH) is a 64 x 64 unitary O (x) P -> I (x) F, with P = F = C^8 and source |0>. The loss is a purity residual sum ||M M^dagger - 1||^2 over random Haar local unitaries, with and without qubit ancillas, plus a penalty on the off-diagonal part of W (classicality), minus the value of a PF-hull facet from orbit 82 (D.7) under a random symmetry. A point with purity residual ~0, W diagonal and facet > 0 would be a purifiable process outside conv(PF).
- Random start (U0 = 1, 8 seeds x 20,000 Adam steps): purity was never reached. The final residual (20 fresh samples, qubit ancillas) was 10-172. The facet values there are meaningless, because W is not normalised. **[failed: the optimiser does not even find pure unitaries from random starts]**
- Start at the Lugano lift (exactly pure, facet image chosen tight = 0 at Lugano; 8 seeds): the search trades purity against violation. Final facet violation was 0.008-0.018 at purity residual 0.13-2.4 (ancilla samples) and off-diagonal mass 4e-5 to 7e-4. Not one run kept both residuals near 0 with positive violation.

This is consistent with the conjecture: leaving the hull at a Lugano vertex costs purity at once, as in D.8's boundary test. It is local, small-sample evidence, not a proof. No counterexample was found.

### H.4 Summary
- Proved: H.1 (some party last implies PF mixture) and H.2 (classically causally separable implies mixture of causally ordered PFs). On both classes the conjecture holds trivially. Also proved: marginal "firstness" does not reduce (E_ex1).
- Settled negatively (H.5): purifiability plus marginal firstness does not force valid conditionals; a 4-term PF mixture is an exact counterexample.
- Failed: the single-vector determinantal bound for orbit 8 (numerically the cone has rank ~51-55 points), and the unitary-side counterexample search (no hit).

### H.5 Purifiability plus "A marginally first" does not force valid conditionals [proved, exact counterexample] (Oct 21 2026)

**Question.** Does purifiable + (A marginally first) imply that every conditional q_{a,x}(b,c|y,z) is a valid bipartite process? If so, H.2 would settle E_ex1 and orbits 7, 8 and 50.

**Answer: no, already for classically purifiable processes.** Take three binary parties and

    p(a,b,c|x,y,z) = (1/4) [a = b + c + y + z mod 2].

- p is a uniform mixture of 4 process functions w_{beta,gamma}: b = beta, c = gamma, a = beta + gamma + y + z. In each, B and C are first and A is last. So p is purifiable (C.1); A is even last (H.1).
- A is marginally first: p(a|x,y,z) = 1/2 for every a, x, y, z.
- The conditional q_a(b,c|y,z) = (1/2)[b + c + y + z = a] is invalid. With the interventions y = b, z = c, sum_{b,c} q_a = 2 for a = 0 and 0 for a = 1.

All of this is checked in exact rational arithmetic (code/stochastic/structural/margfirst_cex.py): the decomposition, validity of p, that the 4 maps are process functions, marginal firstness and the conditional sums. So the implication fails. No search was needed. Any statement of this form is false whenever some PF mixture is marginally first with invalid conditionals.

**Where the naive proof breaks.** The plan was to fix A's classical input and obtain a lift of the conditional. Marginal firstness is a property of the diagonal W only. In the purification (here the source-sink lift of a PF mixture), A's input register is computed downstream of B's and C's outputs. Its marginal is uniform only because the mixture is averaged over (beta, gamma). Fixing a is therefore post-selection on a variable that depends on y, z. Post-selection is not a unitary operation and does not preserve purity or even validity of what remains. A sound conditioning step needs A to be first *in the purifying unitary*: I_A must depend only on the source under every local intervention. That is a structural property of V, not of W. D.4 shows such structure cannot be read off W.

**Consistency with E_ex1 (3) [proved].** E_ex1 is marginally first with invalid conditionals (H.1). Its non-purifiability rests only on the inertia certificate of C.2. H.5 shows that the invalid conditionals carry no evidence by themselves, since a purifiable process shares both features. The certificate is unaffected.

**Consequence.** Route A, in its W-level form, cannot reach the marginally-first orbits. A version that could survive: "if V purifies W and A is first *in V* (I_A independent of all party outputs, as an operator statement), then the conditionals of W are valid". This is proved in H.6 (Lemma H.6.1, Theorem H.6.2). It says nothing about E_ex1 unless one also shows that every purification can be rearranged so that a marginally-first party is first in V. H.5 shows that rearrangement is impossible in general (in the example, A is last in the natural purification). So this line does not by itself settle the conjecture: it reduces it to purifications with no operator-first party (H.6).

### H.6 Operator-level firstness forces valid conditionals [proved] (Oct 21 2026)

This is the operator-level variant left unproved at the end of H.5. Setting as in D: a purification of W is a unitary V : P (x) O -> F (x) I, with O = O_A O_B O_C, I = I_A I_B I_C and a fixed source state |psi>, such that closing the party slots with arbitrary local unitaries (with ancillas) always gives a unitary (AFNB 2017, Def. 3).

**Definition (operator-level first).** Party A is *first in V* if V factorises as

    V = (V' (x) 1_{I_A}) (S (x) 1_O),    S : P -> I_A (x) R unitary,    V' : R (x) O_A (x) O_B (x) O_C -> F (x) I_B (x) I_C unitary,

up to reordering of wires. So I_A is prepared from the source alone, and A's output O_A enters only V', together with the leftover source R. Two other candidate definitions are equivalent:
- (no-signalling form) the channel P (x) O -> I_A obtained from V by tracing F, I_B, I_C does not depend on the O input. Its Choi operator is J_{I_A P} (x) 1_O / d_O. The factorisation follows from Eggeling-Schlingemann-Werner (semicausal => semilocalizable, EPL 57, 782 (2002)) applied to the isometry V. The converse is immediate. [cited + proved]
- (causal-graph form) in the causal structure of the unitary process (Barrett-Lorenz-Oreshkov, Nat. Commun. 12, 885 (2021), Def. 4), with the source and sink as extra nodes, A has no parents among A, B, C. A's own output is included, so there is no self-loop. For unitaries, no influence from each of O_A, O_B, O_C separately implies no influence from O jointly. In the Heisenberg picture, V^dag (Z_{I_A} (x) 1) V commutes with the operator algebras of O_A, O_B and O_C, and these generate all operators on O. [proved]

Firstness is not a property of W: H.5 shows a marginally first party that is last in the natural lift. A weaker "process-level first" condition, that A's input is unaffected by other parties' instruments, is just marginal firstness for classical W. H.5 refutes the reduction under that weaker condition.

**Lemma H.6.1 [proved].** Suppose A is first in a purification (V, psi) of a classical process p(a,b,c|x,y,z). Write S|psi> = sum_a |a>_{I_A} (x) |r_a>_R. Then:
1. A is marginally first, with p(a) = ||r_a||^2.
2. For every a with p(a) > 0 and every x, the pair (V', |r_a>|x>_{O_A} / ||r_a||) is a purification, in the sense of AFNB, of a diagonal bipartite process on B, C whose diagonal is exactly the conditional q_{a,x}(b,c|y,z) = p(a,b,c|x,y,z)/p(a).
3. In particular every q_{a,x} is a valid, purifiable bipartite classical process.

*Proof.*
- (Purity of V'.) Close the A slot with any unitary U_A : I_A (x) X_A -> O_A (x) Y_A (one exists for suitable ancilla dimensions), and close B and C with arbitrary U_B, U_C. Because nothing upstream of I_A depends on any output, contracting the A wire is ordinary sequential composition:

      M = (M'_{BC} (x) 1_{Y_A}) (1_R (x) U_A (x) 1_{X_B X_C}) (S (x) 1_{X_A X_B X_C}),

  where M'_{BC} : R (x) O_A (x) X_B (x) X_C -> F (x) Y_B (x) Y_C is V' with B and C closed. M is unitary because V is pure. The two right-hand factors are unitary. So M'_{BC} (x) 1 is unitary, and hence M'_{BC} is unitary. This holds for all U_B, U_C, so V', with source R (x) O_A, is a pure bipartite process.
- (Diagonal and conditionals.) V|psi,x,y,z> = sum_a |a>_{I_A} (x) V'|r_a,x,y,z>. The Choi entries of W are therefore W[(a,b,c,x,y,z),(a',b',c',x',y',z')] = <V'(r_{a'},x',y',z')_{b'c'} | V'(r_a,x,y,z)_{bc}>_F, where _{bc} denotes the component with I_B I_C = |b,c>. For a = a' and x = x', these are the entries of p(a) times the process matrix W'_{a,x} of (V', |r_a,x>/||r_a||). W is diagonal, so W'_{a,x} is diagonal with diagonal p(a,b,c|x,y,z)/p(a) = q_{a,x}. Summing the diagonal over b, c at y, z gives sum_{b,c} ||V'(r_a,x,y,z)_{bc}||^2 = ||r_a||^2, which is item 1.
- (Validity.) The diagonal of a valid process matrix is a valid classical process: evaluate it on the measure-and-prepare channels b -> g(b). Validity of W'_{a,x} follows from purity (Appendix A). ∎

**Where the H.5 obstruction went.** With A's slot replaced by a SWAP to ancillas, the remaining B, C map from P (x) O_A to F (x) I_A is unitary for every pure process, whether or not A is first (checked numerically below). So the source-and-sink "open-A" bipartite process is always pure. The conditioning on x is harmless, since x is a source preparation. The conditioning on a is a sink post-selection. Firstness is exactly what moves the a-measurement onto R, before V' acts, via S. Normalisation then comes for free (item 1). Without firstness, a is a sink outcome, and fixing it is the post-selection of H.5.

**Theorem H.6.2 [proved].** Let W be a 3-party classical process (any finite alphabets). If some purification of W has some party first at the operator level, then W is a PF blend, indeed a blend of causally ordered process functions with that party first.

*Proof.* Lemma H.6.1 shows that the party is first with valid conditionals. Apply H.2, which uses G.1. ∎

*N parties.* Lemma H.6.1 holds verbatim and gives an (N-1)-party purifiable conditional. If the conditional purifications again have a first party, recursively, W is a blend of causally ordered PFs. For the conditional, that party has to be first in V' with the source state |r_a,x>, so the recursion is on V', not on W. This includes the case where V has an acyclic causal structure in the BLO sense: a topological order supplies a first party at every level, and the order is inherited by V'. The 3-party case needs firstness only once, because G.1 handles every bipartite remainder. [proved for N = 3; for N > 3, proved under the recursive hypothesis, using the recursive form of H.2 stated after its proof]

*Quantum remark.* For a general (non-diagonal) W, the same proof gives a pure bipartite conditional. BLO Theorem 3 (every unitarily extendible bipartite process is causally separable) then makes W causally separable with A first. [proved modulo cited BLO Thm. 3]

**Contrapositive (useful) [proved].** If W is not first-with-valid-conditionals in party k, then no purification of W has k first at the operator level. Consequences:
- Lugano is not marginally first in any party (H.1), so none of its purifications, not just the lift, has an operator-first party.
- None of E_ex1 or the 51 sampled non-deterministic vertex orbits is first-with-valid-conditionals in any party (H.1 numerics). So a purification of any of them, if one exists, has no operator-first party. This includes orbit 8, which is marginally first in parties 1 and 2. For E_ex1 and orbits 7 and 50 the statement is vacuous, since they have no purification at all (C.2).

**What this leaves open.** The conjecture is now reduced to purifications in which **every** party has a parent among the party outputs, i.e. every party's input is influenced by some output in V. Lugano-type lifts are like this: their causal graph is a 3-cycle. Theorem H.6.2 says nothing about a W whose only purifications are of this kind. That is the same class flagged as open in Section 9, now characterised at the operator level. A purifiable non-blend, if one exists, must be such a W: one with no first party and no last party in any purification. W-level lastness already gives H.1. Operator-level lastness is a stronger hypothesis, so it is covered too.

**Numerics [numerical]** (code/stochastic/structural/opfirst.py, log opfirst.log; C.1 lifts). The firstness residual is max |J - Tr_O J (x) 1/d_O| for the channel P (x) O -> I_k. Open purity is ||M M^dag - 1||_max, with slot k replaced by a SWAP and the other two closed by Haar unitaries with qubit ancillas, worst of 5.

| process | party | op-first residual | open-slot purity | marginally first | conditionals |
|---|---|---|---|---|---|
| Lugano | A, B, C | 0.75 each | <= 1.3e-15 | no | n/a |
| H.5 blend | A | 0.5 (not first) | 8.9e-16 | yes | invalid (sums 0, 1, 2) |
| H.5 blend | B | 0 (first) | 1.4e-15 | yes | valid (all sums 1) |
| H.5 blend | C | 0 (first) | 1.1e-15 | yes | valid |

This is consistent with the lemma. In the H.5 lift, A is last and not operator-first, and its conditionals are invalid. B and C are operator-first, and their conditionals are valid, as H.6.1 requires. The open-slot map is unitary in every case, which confirms that the content of the lemma is the source-side relocation of the a-measurement.

**Literature [cited, checked against arXiv:2002.12157v3 and quant-ph/0104027].**
- Barrett, Lorenz and Oreshkov (2021) prove the two endpoints. If a unitary process has an acyclic causal structure, it is a comb (Thm. 4). Every unitarily extendible bipartite process is causally separable (Thm. 3). Their Thm. 6 is that reversibly extendible classical processes form the deterministic polytope, the classical analogue of D.6.
- They state that a unitarily extendible process need not be causally separable in general (AF process), and they leave open how cyclicity constrains extensions. I did not find the one-parentless-node conditioning lemma H.6.1, or Theorem H.6.2, stated there, in AFNB 2017, or in Wechs-Abbott-Branciard 2019. WAB's recursive definition of causal separability (first party, then a valid conditional) is the target property; they do not connect it to purifications. H.6.1 is elementary given those sources. It is offered as a short observation, not as a new technique. I did not do a full literature search beyond these papers.

## References

1. M. Dummett, Can an effect precede its cause?, Aristotelian Society Supplementary Volume 28, 27 (1954); Bringing about the past, Philosophical Review 73, 338 (1964).
2. M. Black, Why cannot an effect precede its cause?, Analysis 16, 49 (1956).
3. D. Lewis, The paradoxes of time travel, American Philosophical Quarterly 13, 145 (1976).
4. K. Gödel, An example of a new type of cosmological solutions of Einstein's field equations of gravitation, Reviews of Modern Physics 21, 447 (1949).
5. M. S. Morris, K. S. Thorne and U. Yurtsever, Wormholes, time machines, and the weak energy condition, Physical Review Letters 61, 1446 (1988).
6. J. Friedman, M. S. Morris, I. D. Novikov, F. Echeverria, G. Klinkhammer, K. S. Thorne and U. Yurtsever, Cauchy problem in spacetimes with closed timelike curves, Physical Review D 42, 1915 (1990).
7. F. Echeverria, G. Klinkhammer and K. S. Thorne, Billiard balls in wormhole spacetimes with closed timelike curves: classical theory, Physical Review D 44, 1077 (1991).
8. A. Carlini, V. P. Frolov, M. B. Mensky, I. D. Novikov and H. H. Solodukhin, Time machines: the Principle of Self-Consistency as a consequence of the Principle of Minimal Action, International Journal of Modern Physics D 4, 557 (1995).
9. J. Earman, Bangs, Crunches, Whimpers, and Shrieks: Singularities and Acausalities in Relativistic Spacetimes, Oxford University Press (1995).
10. D. Deutsch, Quantum mechanics near closed timelike lines, Physical Review D 44, 3197 (1991).
11. S. Aaronson and J. Watrous, Closed timelike curves make quantum and classical computing equivalent, Proceedings of the Royal Society A 465, 631 (2009).
12. C. H. Bennett, D. Leung, G. Smith and J. A. Smolin, Can closed timelike curves or nonlinear quantum mechanics improve quantum state discrimination or help solve hard problems?, Physical Review Letters 103, 170502 (2009).
13. S. Lloyd et al., Closed timelike curves via postselection: theory and experimental test of consistency, Physical Review Letters 106, 040403 (2011).
14. O. Oreshkov, F. Costa and Č. Brukner, Quantum correlations with no causal order, Nature Communications 3, 1092 (2012).
15. Ä. Baumeler and S. Wolf, The space of logically consistent classical processes without causal order, New Journal of Physics 18, 013036 (2016).
16. Ä. Baumeler, F. Costa, T. C. Ralph, S. Wolf and M. Zych, Reversible time travel with freedom of choice, Classical and Quantum Gravity 36, 224002 (2019), arXiv:1703.00779.
17. M. Araújo, A. Feix, M. Navascués and Č. Brukner, A purification postulate for quantum mechanics with indefinite causal order, Quantum 1, 10 (2017).
18. A. Vanrietvelde, N. Ormrod, H. Kristjánsson and J. Barrett, Consistent circuits for indefinite causal order, arXiv:2206.10042 (2022).
19. H. Price, Does time-symmetry imply retrocausality? How the quantum world says yes, Studies in History and Philosophy of Modern Physics 43, 75 (2012).
20. M. S. Leifer and M. F. Pusey, Is a time symmetric interpretation of quantum theory possible without retrocausality?, Proceedings of the Royal Society A 473, 20160607 (2017).
21. T. Maudlin, A tale of two tensors, or, how not to argue for retrocausality, preprint (2017).
22. E. Specker, Die Logik nicht gleichzeitig entscheidbarer Aussagen, Dialectica 14, 239 (1960).
23. H. Dourdent, A. Leitherer, E.-C. Boghiu, K. Simonov, R. Kunjwal and A. Acín, What makes a causal loop consistent?, arXiv:2609.39735 (2026).
24. N. Daher Ahmed and R. Kunjwal, Characterizing unitaries via quasi-process functions, arXiv:2610.00579 (2026).
25. J. Faye, Backward causation, Stanford Encyclopedia of Philosophy, substantive revision 28 October 2025.
26. L. M. Tolksdorf and R. Verch, Quantum physics, fields and closed timelike curves, Communications in Mathematical Physics 357, 319 (2018).
27. Ä. Baumeler, A. S. Gilani and J. Rashid, Unlimited non-causal correlations and their relation to non-locality, Quantum 6, 673 (2022).
28. G. Tobar and F. Costa, Reversible dynamics with closed time-like curves and freedom of choice, Classical and Quantum Gravity 37, 205011 (2020), arXiv:2001.02511.
29. H. Dourdent, K. Simonov, A. Leitherer, E.-C. Boghiu, R. Kunjwal, S. Halder, R. Augusiak and A. Acín, Paradox-free classical non-causality and unambiguous non-locality without entanglement are equivalent, arXiv:2512.23599 (2025).
30. Ä. Baumeler, Causal loops: logically consistent correlations, time travel, and computation, PhD thesis, Università della Svizzera italiana (2017).
31. V. Baumann and Č. Brukner, Appearance of causality in process matrices when performing fixed-basis measurements for two parties, Physical Review A 93, 062324 (2016).
