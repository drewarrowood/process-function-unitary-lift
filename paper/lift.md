# Purifiable classical processes need not be mixtures of process functions

*Subtitle: every process function lifts to a unitary process, but quantum purifiability strictly enlarges the classical-process set beyond the process-function hull (three binary parties).*

**Draft note. Not submitted. Not refereed.** Canonical source of the paper; `lift.pdf` is built from this file.

## Abstract

A classical process (a point of the Baumeler-Wolf polytope) is purifiable in the sense of Araujo et al. (2017) if it arises from a pure process, one that stays unitary under all local unitaries with ancillas, by restricting to classical interventions. Mixtures of process functions are purifiable, and it was natural to ask whether nothing else is; we had conjectured so. **The main result of this note is that this is false.** Theorem H.12.1 gives a three-party binary classical process p, induced by an explicit Switchboard with eight 8x8 boards whose entries lie in Z[i]/8 and a source state with phases in Q(zeta_8), such that p is valid, the machine is pure, and p violates a facet inequality of the process-function (PF) hull: L(p) = 1/4 - (3/16) sqrt 2 < 0, while L >= 0 on all 744 process functions. The verification is exact. It has been re-derived independently from the paper text alone (code/stochastic/cyclic/switchboard/verify_h12), and the statement `purification_conjecture_false : ∃ p, Valid p ∧ Purifiable p ∧ p ∉ convexHull ℝ PFset` is checked by the Lean 4 proof assistant with Mathlib (lean/PFUL/Counterexample.lean; standard axioms only, no `sorry`, no `native_decide`). Two gaps remain in the formal statement: ancillas are finite-dimensional, and the Lean definitions of purity, validity and process function are self-contained, not yet linked to the PFUL.Validity/Choi framework used elsewhere in the repository. The paper has not been peer reviewed.

The counterexample sits exactly where earlier structural results said it must. If some party is first at the operator level in a purification, the process is a PF blend (H.6); in the counterexample no party is first, and every party's input depends on another party's output. For two parties every valid classical process is a PF blend (Appendix G), so three parties are needed. Classically reversible purification gives exactly the PF hull (D.6), so the gap is a quantum effect. Exact non-purifiability certificates for E_ex1 and two vertex orbits (C.2) show the purifiable set is still a proper subset of the valid processes.

The first part of the note proves the lifting theorem that the purification question starts from. A process function is a classical map w from the outputs of several parties to their inputs such that every choice of local deterministic interventions has exactly one fixed point. Baumeler, Costa, Ralph, Wolf and Zych showed that every process function extends to a bijection by adding a source and a sink, and left open whether every such bijection quantizes to a valid unitary quantum process; Daher Ahmed and Kunjwal (2026) state this as a conjecture and prove it for a subclass. We give a short argument that it holds for every process function with finite alphabets: the permutation unitary U|o,e> = |w(o)+e, o> composed with arbitrary local unitaries induces a unitary from source to sink. The key combinatorial fact, that two distinct output strings always disagree at some party whose input w assigns equally, is the pairwise-exclusivity property of Dourdent et al. (2026). The identity M M^dagger = 1 and the validity chain are machine-checked in Lean 4 (PFUL.induced_unitary, PFUL.valid_kraus, PFUL.valid_instrument, PFUL.Choi.bornC_anc_eq_one, PFUL.Choi.afnb_iff_density, PFUL.Choi.isCP_iff_choi, PFUL.Choi.validity_package; standard axioms only), and Appendix F extends it to countable alphabets (PFUL.Countable.induced_unitary_l2). The Choi form in infinite dimensions is formalised as a convergent Born-pairing series (Section 9), and continuous alphabets are settled only partly (F.5: point-map local operations, or causal w). The philosophical sections read the lifting theorem as saying that fixed-point consistency is already a quantization condition, and Section 10 reads H.12 as saying that purity does not, in addition, single out mixtures of deterministic loops. Section 9 states exactly what is proved, certified, numerical, or open.

## 0. Introduction and contributions

Process functions are the deterministic classical processes without global causal order: every local choice has exactly one consistent history. Their mixtures form a polytope, conv(PF), inside the larger polytope of valid classical processes. Purity (unitarity under all local operations, Araujo et al. 2017) is the standard candidate for the physically admissible processes. Two questions follow: does every process function purify, and are mixtures of process functions the only classical processes that do? This note answers the first yes and the second no.

Contributions, in the order of the evidence for them:

1. **A purifiable classical process outside the PF hull (Theorem H.12.1) [proved; exact; independently re-derived; Lean-checked with two stated gaps].** Three binary parties, an explicit X-type Switchboard and source state, a facet inequality of conv(PF) violated by 1/4 - (3/16) sqrt 2. Section 9 and H.12 list what each check covers.
2. **Every process function lifts to a unitary process (Section 1, Appendix A) [proved; Lean-checked in finite dimensions; countable alphabets in Appendix F].**
3. **Where purifiable non-blends can and cannot live [proved].** Mixtures of PFs are purifiable (C.1). Two parties: every valid classical process is a PF blend (Appendix G). Three parties: a party last, or a party first with valid conditionals, forces a PF blend (H.1, H.2), and so does a party that is first at the operator level in some purification (H.6). Switchboard structure: the purity conditions are an operator form of pairwise exclusivity, ancillas add nothing, and commuting or two-term boards give PF blends (H.8, H.10.6).
4. **Limits of the purifiable set [certified exact].** E_ex1 and vertex orbits 7 and 50 are not purifiable (C.2), so the purifiable set lies strictly between conv(PF) and the valid polytope.
5. **The complete facet list of the three-party binary PF hull** (29,344 facets in 93 orbits, D.7), negative results for several certificate routes (D.8, Appendix E, C.5, C.6), and numerical surveys, all labelled as such.

Earlier versions of this note stated the "only if" direction as a conjecture and collected evidence for it. That material is kept as a record and marked superseded where H.12 overturns it; nothing in it is used in the proof of H.12.1.

**Novelty and prior work (literature check of Oct 23 2026).** Status of each main claim, as far as we could find:
- *Purifiable classical processes beyond conv(PF) (H.12.1, H.13.2) and convexity of Purif (H.13.1): new, as far as we can tell.* The inclusion conv(PF) ⊆ Purif was asserted earlier by Baumeler, Gilani and Rashid (Quantum 6, 673 (2022), ref. 27), without a separate proof for the coherent operator. We found no published statement of the converse ("purifiable classical = mixture of PFs"); it appears to be our own conjecture (C.3), and we found no earlier proof or counterexample. AFNB 2017 ask a different question (are all extensibly causal processes purifiable?). The nearest open question is Kunjwal and Oreshkov's (arXiv:2307.02565, ref. 36): can correlations from unitarily extendible process matrices be antinomic? We do not answer it. The H.13.2 correlation lies inside the (3,2,2) nomic polytope (H.13.5).
- *Every process function lifts to a unitary process (Section 1, Appendix A; countable alphabets, Appendix F): partly known.* Baumeler, Gilani and Rashid asserted it without a coherent-level proof. It was proved for the Lugano process (AFNB 2017, Section 7), for an n-party family (Araújo, Guérin and Baumeler, PRA 96, 052315 (2017), Appendix B, ref. 37), and for MECC unitaries (Daher Ahmed and Kunjwal, arXiv:2610.00579, Theorem VII.1, ref. 24). Those last authors state the general case as Conjecture VII.1. Our general proof appears to settle it (Section 6). We found no earlier treatment of countable alphabets.
- *The X-type term threshold (H.14.1: boards with at most three terms always give PF blends; four terms can leave the hull): new.* It is stated in terms of this note's Switchboard definitions, and we found nothing comparable.
- *No single-use fine-grained model for H.13.2 (H.15.7b): an application of known results.* That single-use acyclic and QC-QC realisations give causal correlations is due to Wechs, Dourdent, Abbott and Branciard (PRX Quantum 2, 030335 (2021)) and related work. What is ours is the exact causal-inequality certificate for this particular purifiable non-blend. Lugano, a PF, already violates causal inequalities, so "purifiable but not QC-QC" is not new in itself.

Coverage caveat: we searched by web search and read the primary sources cited here. We did not run a systematic citation-graph or Google Scholar search, and preprints from the last few weeks may be missing.

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

Daher Ahmed and Kunjwal (arXiv:2610.00579, 30 September 2026, ref. 24) state as Conjecture VII.1: "Any process function can be purified to a unitary process." They support it numerically and prove it for unitaries with mutually exclusive control conditions (MECC; their Theorem VII.1), and under a second sufficient condition, unambiguity. They note that the bare permutation unitary of the reversible extension may fail to be a valid process. The argument below is that it does not fail. As far as we can tell, it settles Conjecture VII.1 for all process functions with finite alphabets, and Appendix F extends it to countable alphabets (Hilbert spaces ℓ²). Earlier special cases are the Lugano process (AFNB 2017, Section 7, below) and an n-party family of AF/BW-type processes, for which Araújo, Guérin and Baumeler (PRA 96, 052315 (2017), Appendix B, ref. 37) prove validity of the coherent purification. Araújo, Feix, Navascués and Brukner had already written down, in 2017, a purification of the Lugano process by exactly this construction (the standard |x,y> -> |x, y + f(x)> trick, credited there to Baumeler and Wolf); a routed-circuit reconstruction is due to Vanrietvelde, Ormrod, Kristjánsson and Barrett. Baumeler, Gilani and Rashid (2022) proved that the diagonal (dephased) process matrix of every process function is valid, and remarked, without a separate proof for the coherent operator, that the reversible extensions are therefore unitarily extensible. The contribution claimed here is a short general proof for the coherent permutation unitary, for every process function.

## 7. Time symmetry and retrocausality

Price has argued that a time-symmetric ontology for quantum theory should be retrocausal, on the assumption that the quantum state is real. Leifer and Pusey replaced that assumption with lambda-mediation: correlations between a preparation and a later measurement are mediated by the ontic state of the system. No retrocausality, operational time symmetry, and lambda-mediation then imply a timelike Bell factorization, which sequential measurements violate. Maudlin's reply is that the operational time-reverse of an experiment is not always itself an experiment of the same kind. The no-go is conditional.

The dilation in this note is adjacent to that argument, not a solution of it. A process function that violates a causal inequality already has each party's input depending on another party's output. The later setting is an argument of the earlier input. Lambda-mediation, in the strict past-screening sense, fails because of the cycle, not because a retrocausal hidden variable was added by hand. Read forwards, the source is an input and the sink is an output. Read backwards, they exchange roles, and the inverse of the permutation unitary is the reversed process. The objection that the bare Lugano function is not an involution on its own three bits is an objection to refusing the source and the sink. Whether the dependence is the retrocausality Price asked for, or only an operational time-reverse, is a reading of the same operator. The mathematics does not choose the reading. It does remove one cheap reply: one cannot say that the cyclic classical model dies when instruments become unitary.


## 8. What this does not settle

Embeddability is untouched. A unitary process on a finite alphabet is not a solution of Einstein's equation, and it is not a local Hamiltonian flow on a wormhole. The billiard has the wrong multiplicity. Post-selection realises the event list conditional on the post-selection succeeding. The theorem says the list has a unitary dilation. It does not say the dilation is a spacetime.

Purifiability in the sense of open quantum problem 43, whether every extensibly causal process is purifiable, is related but not identical. The theorem puts every process function, including those that violate causal inequalities, inside the unitarily extendible fragment. It does not classify processes that are not deterministic classical functions.

Freedom is not settled. Nothing here decides whether an agent whose output is an argument of an earlier input has a choice. The fixed-point clause says the choice, if made, completes uniquely. It does not say the choice was open. Whether this is an adequate reply to Black depends on whether consistency conditions may rule out interventions, or only rule out histories given the interventions. The note takes the second reading: consistency rules out histories given the interventions, never the interventions themselves (Section 5), and the formalism is built for it.

The combinatorial lemma is finite for any fixed alphabet and is the piece an attacker has to break. The linear algebra after it is row orthogonality. See lean/STATUS.md for exactly what is and is not machine-checked.


## 9. Status: what is proved about purifiable classical processes

**Former conjecture.** A classical process is purifiable if and only if it is a mixture of process functions (a "PF blend").

**Theorem 9.1 (= H.12.1) [proved].** The "if" half holds (C.1). The "only if" half is false: there is a valid three-party binary classical process that is purifiable and lies outside conv(PF).

What supports Theorem 9.1, in decreasing order of independence:
- *Exact paper proof* (H.12, code/stochastic/cyclic/switchboard/c1/exact_cex.py). Exact arithmetic in Q(zeta_8): unitarity of the boards, the Pauli rule of H.8.1, validity under all 64 deterministic interventions, and the facet value 1/4 - (3/16) sqrt 2 < 0. Purity then follows from the paper proofs of H.7.1, H.8.1 and H.8.2.
- *Independent re-derivation* (verify_h12/verify.py, verify.log), written from the paper text only. It checks purity directly through an exact multi-affine criterion over 125 slot combinations, with no use of H.7.1 or H.8. It re-enumerates the 744 PFs by brute force over 8^8 maps and uses its own rational separating inequality, value 1 - (3/4) sqrt 2 < 0, together with an infeasible membership LP. It also runs 1,200 random float trials (residual <= 2.4e-15) with a perturbed control.
- *Lean 4 proof* (lean/PFUL/Counterexample.lean, CounterexampleData.lean; lean/STATUS.md Round 6). The statement `purification_conjecture_false : ∃ p, Valid p ∧ Purifiable p ∧ p ∉ convexHull ℝ PFset` is proved. The only axioms are propext, Classical.choice and Quot.sound. There is no `sorry` and no `native_decide`; the finite computations use `decide +kernel`. Purity is proved for all finite ancillas and local unitaries (`isPure_Vsb`), validity for all stochastic local interventions (`valid_pcl`), and non-membership through the facet functional (`pcl_not_mem_convexHull`). **Gaps:** (i) ancillas range over finite types only; (ii) `Valid`, `Purifiable` and `PFset` are defined in that file, finite-dimensionally, and are not yet proved equivalent to the PFUL.Validity/Choi definitions used for the lifting theorem. A reader has to check that those definitions mean what Section 9 says (H.12.3 lists them).

None of this has been peer reviewed.

**Where the gap lives.** It needs three parties (Appendix G), a purification with no operator-first party (H.6), and boards that are neither commuting nor two-term (H.8.4, H.10.6). The H.12 machine has all three features.

This section is a map of the current status. Labels follow the appendices: **[proved]**, **[certified exact]** (rational certificate, not Lean), **[numerical]**, **[cited]**. Proofs live in the appendices and are not restated here.

**Proved.**
- *Process functions lift* (Section 1, Appendix A). Every process function lifts to a unitary process. The core identity and the validity chain are machine-checked in Lean in finite dimensions (PFUL.induced_unitary; PFUL.Choi.validity_package). Countable alphabets: Appendix F (PFUL.Countable.induced_unitary_l2). Continuous alphabets (F.5): measure preservation for every measurable process function and unitarity for point-map local unitaries (all local unitaries if w is causal) are proved in the paper, with the combinatorial core in Lean (PFUL.Continuous); a canonical closed loop for non-causal w with general local unitaries is open.
- *Blends lift* (C.1). Every mixture of process functions is purifiable, and convex combinations of purifiable processes are purifiable. This is the "if" half of the former conjecture.
- *Classical version* (D.6). A classical process is classically reversibly purifiable iff it is a PF blend. Together with H.12 this shows that quantum purifiability does add something: the quantum purifiable set strictly contains the classical one.
- *Two parties* (Appendix G, Theorem G.1). Every bipartite valid classical process, with any finite alphabets, is a blend of causally ordered process functions. So for two parties purifiable = PF blend = valid; the gap of H.12 needs three parties. This is known in substance [cited: Oreshkov-Costa-Brukner 2012, Suppl.; Baumann-Brukner 2016].
- *Three parties, a party last* (Theorem H.1). If some party's output influences nothing, the process is a PF blend.
- *Three parties, causally separable* (Theorem H.2). If some party is first and every conditional bipartite process is valid, the process is a PF blend. So every classically causally separable three-party process is a blend of causally ordered process functions, so no gap can occur on that class.
- *Three parties, a party first in the purification* (Lemma H.6.1, Theorem H.6.2). If some purification of W has a party whose input is prepared from the source alone (operator-level first: V factorises through that party's input), then every conditional bipartite process is valid and purifiable, and W is a PF blend. So a purifiable process outside the hull can only have purifications in which every party's input is influenced by some party output. Lugano has no purification with an operator-first party.
- *Switchboard structure* (H.8). The H.7.1 purity conditions are equivalent to a Pauli-span condition, K_{o,o'} in the span of the operators trivial on some party whose output changed, which is the operator form of exclusivity. Checked in exact arithmetic. Ancillas add no conditions, so H.7.1 is full purity. Operator-first and operator-last parties are read off K. Monomial or commuting switchboards give PF blends for every source state (H.8.1-H.8.5).
- *Attacks on (C1)* (H.10). Two natural routes are closed. No twirl that preserves p can reduce to the commuting case, and the degree-2 (Shor) relaxation in the board entries is vacuous. Exhaustive check: pairwise exclusivity is equivalent to being a PF for three binary parties (744). Two-term boards X^{w1(o)} exp(i t X^{d(o)}) are classified exactly (39,512 non-trivial pairs, 34,304 with non-commuting projectors).
- *Toward (C2)* (H.11). Input copying preserves purity. Generalized switchboards (extra sink F') obey the block-wise Pauli rule. (C2) reduces to whether the sink can be made to record o on every source state (open).
- *Robustness, trivial halves* (I.1-I.3). Being eps-close to a blend implies being eps-close to purifiable. A quantitative converse would have been equivalent to the conjecture, and is therefore false (H.12). In family C the machine residual bounds the operator purity defect.
- *Structure of purifications* (D.1, D.2, D.5). The sink records (o, i) orthogonally. Constraints on the fixed source state are vacuous. Validity under quantum-controlled interventions holds for every classical process.

**Certified exact non-purifiable.** E_ex1, and vertex orbits 7 and 50 (one of which contains E_ex1): exact inertia certificates (C.2; code/stochastic/cert). So the purifiable set, while larger than conv(PF), is still a proper subset of the valid classical processes.

**Settled negatively (routes that provably do not work).**
- *Hidden source label* (D.3/D.4). The single-classical-label strengthening D.3 is false: a causal circuit is an exact counterexample.
- *Fixed-source certificates* (D.8). No certificate that uses only the fixed source sector can rule out purification of any classical process.
- *Marginally-first reduction* (H.5). Purifiability plus "party A's input marginal is output-independent" does not force valid conditionals. The operator-level version does (H.6). An exact counterexample is a 4-term PF blend. So H.2 cannot be extended this way to E_ex1 and orbits 7, 8, 50, even though all of them are marginally first in some party (H.1 numerics).
- *Form-based certificates for orbits 8/10/20* (C.5). Every linear or block-Hermitian combination of the constraint forms tried stalls at lambda_16 ~ +1e-4. Adding the Gram normalisation provably adds nothing. The obstruction is non-convex. The earlier estimate that "about half" of the open orbits are certifiable by the current pipeline is **withdrawn**.
- *Moment relaxation* (Appendix E). The degree-2 relaxation is feasible for E_ex1, so it is weaker than single-form inertia.
- *Degree-4 single-vector certificates for orbit 8* (C.6) [numerical]. Random 67-dim (even 60-dim) subspaces of V_W, with the radical removed, contain jointly isotropic vectors (loss 1e-9 to 2e-7, against a baseline of 0.1). So the C.5 degree-4 proposal fails for random L, and full-frame level-2 Lasserre is about 3.4e6 in size. No paid compute was used.
- *Single-vector determinantal bound for orbit 8* (H.2 route B) [numerical]. The jointly isotropic cone contains vectors with rank K(u) of about 51-55, so the bound gives only dim <= ~28-32, not < 16.

**Numerical observations (not proof; recorded before H.12 and partly read at the time as support for the conjecture, which H.12 shows they were not).**
- *GPU sweep* (C.4). None of the 49 remaining sampled non-deterministic vertex orbits lifted. Best residuals were 12.97-59.35; the same code reaches 1e-16 on Lugano.
- *Isotropic dimension* (C.5). For orbits 8, 10 and 20, constraint-isotropic subspaces appear to exist up to dimension ~10 and fail by 12. A purification needs 16.
- *Facets* (D.7). Facet orbit 82 is violated by E_ex1 and by all 51 sampled non-deterministic vertex orbits.
- *Boundary* (D.8). Along Lugano -> E_ex1, purifiability appears to stop where the PF hull does.
- *Two-term boards* (H.10.4). All 237 symmetry classes, 7 values of t and all 29,344 facets give operator facet values >= -1.7e-14. So they lie in conv(PF) for every source state, including the non-commuting ones. No counterexample. Float64, not exact.
- *Switchboard robustness* (H.8, I.4). Minimising the exact purity residual R at prescribed facet-82 violation v always gave R >= 0.31 v^2, i.e. violation <= 1.79 sqrt(R): 108 runs, v from 0.01 to 0.9. No counterexample in family C was found by this local search; H.12 lies in family C, so the floor is withdrawn (Appendix I).
- *Unitary-side hunt* (H.3). Optimising unitaries for purity, classicality and facet violation found no purifiable process outside the hull (the H.12 example needed the restriction to X-type boards). From Lugano, facet violation of ~0.01 costs a purity residual of 0.1-2.4.

**Refuted / superseded (Oct 22 2026).** The only-if half of the conjecture and the Switchboard conjecture (C1) are false (H.12.1). The Appendix I floor R >= 0.31 v^2 was a local-optimisation artefact and is withdrawn. Evidence items above that were read as support for the conjecture (C.4, D.7, D.8, H.3, H.7, the Switchboard robustness item) remain true as statements about what was found, not as evidence for it.

**Proved (Oct 22, later).** *Coset-transport theorem* (H.10.6): X-type boards whose class-constant selections are all PFs give PF blends for every source state, with an explicit decomposition. Exhaustive exact check: **all two-term boards are PF blends**. *Recording* (H.11.4): a coherent-control purification shows that o need not be recorded on every source state.

## 10. Conclusion, interpretation, and open problems

**What purity singles out.** For process functions purity is automatic (Section 1): fixed-point consistency already guarantees a unitary dilation. For classical processes in general it is a genuine restriction, since E_ex1 and orbits 7 and 50 are valid but not purifiable (C.2). But it is not the restriction "mixture of deterministic consistent loops". The purifiable classical processes form a convex set strictly between conv(PF) and the valid polytope (C.3, H.12). Classically, reversible purification gives exactly conv(PF) (D.6). So the extra processes are a quantum effect. A coherent superposition of board operations, none of which is a classical bijection, yields classical statistics that no mixture of process functions reproduces.

**No operator-first party is needed, and none is allowed.** H.6 shows that if any party is first at the operator level in some purification, the process is a PF blend. Every purifiable non-blend must therefore be "cyclic all the way down": in every purification, each party's input depends on some party's output. The H.12 machine is of this kind (operator-first residuals 0.31 / 0.25 / 0.31, complete causal graph). The gap is not produced by an exotic ingredient such as a party acting before the loop. It comes from the loop itself.

**The two-party contrast.** With two parties every valid classical process is a blend of causally ordered process functions (Appendix G), so valid = purifiable = conv(PF). The separation first appears at three parties, the smallest setting in which process functions without causal order (Lugano) exist.

**Interpretation (philosophical, not a result).** Read a process function as a deterministic consistent time loop. Before H.12, the hoped-for reading was that every reversible quantum loop with classical statistics is an ignorance mixture of such loops: chance in a loop would only be ignorance of which loop obtains. H.12 shows this reading fails. Quantum reversibility admits classical loops whose chance is not ignorance over deterministic loops, though it still excludes some classically consistent ones (E_ex1). The earlier version of this paragraph assumed the conjecture. It is superseded, as is its claim that reversibility excludes basic chance from loops; D.4's caveat about contextual "which-loop" variables no longer bears on the main question.

**Open problems.**
1. *Characterise the purifiable set.* Is it a polytope, or even closed? What are its extreme points? Are vertex orbits 8, 10, 20 and the other 46 sampled orbits that are numerically non-purifiable (C.4, C.5) truly non-purifiable? Exact certificates exist only for orbits 7 and 50.
2. *Minimal counterexamples.* Find the smallest facet violation and the fewest non-PF board terms. Which facet orbits can be violated? The H.12 example uses facet 1741 of the normaliz list. What is the reach of X-type boards? The H.12 boards reach L1 distance 0.828 = 2(sqrt 2 - 1) from conv(PF) at their best source state [numerical]. Are three-term boards enough?
3. *Other scenarios.* Larger alphabets, more parties, unequal alphabets (Appendix B), the countable case (Appendix F), and which causal-inequality violations the new processes reach.
4. *Close the formal gaps.* Link the Lean definitions in Counterexample.lean to PFUL.Validity/Choi, and extend purity to infinite-dimensional ancillas.
5. *Structure of purifications.* The reduction (C2) of a general three-party purification to Switchboard form (H.11) is open, and so is any facet description of the purifiable set derived from purity.

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

Bookkeeping: `PFUL.Choi.bornAnc_eq_one` needs no structure on the ancilla types. `PFUL.Choi.bornSplit_eq_one` and `PFUL.Choi.afnb_iff_density_split` use exactly the index layout of `ValidWith`. `PFUL.Choi.validity_package` bundles unitary validity, Kraus-channel validity and AFNB normalisation in one theorem. Infinite dimensions (countable alphabets). The unitary layer there is `PFUL.Countable.induced_unitary_l2`. Mathlib has no trace-class or Hilbert-Schmidt operators on infinite-dimensional Hilbert spaces, so the project builds them against its pinned Mathlib (`lean/PFUL/TraceClass.lean`, no `sorry`, standard axioms only). Hilbert-Schmidt operators have a basis-independent norm (`PFUL.TraceClass.hsSq_indep`). The trace class is the span of products A†B of Hilbert-Schmidt maps. Its trace Tr T = Σ⟨e_i, T e_i⟩ converges for every Hilbert basis to the same value (`hasSum_trace`). It is linear (`traceL`), cyclic against bounded operators (`trace_comp_comm`), nonnegative on positive operators (`trace_nonneg`), gives Tr|x⟩⟨y| = ⟨y, x⟩ (`trace_rankOne`), is invariant under isometric conjugation (`trace_conj`), and obeys |Tr T| ≤ ‖T‖₁ < ∞ with ‖T‖₁ = sup over ‖C‖ ≤ 1 of |Tr(CT)| (`enorm_trace_le_traceNorm`, `traceNorm_ne_top`). The trace class is a two-sided ideal (`comp_mem_left`, `comp_mem_right`). The partial trace over J is defined on H ⊗ ℓ²(J), realised as ℓ²(J; H), and on ℓ²(I × J) ≅ ℓ²(J; ℓ²(I)) (`l2ProdEquiv`). It is the unique trace-class operator with Tr(Tr_J(T) C) = Tr(T (C ⊗ 1)) for all bounded C (`trace_ptrace_comp`, `ptrace_unique`, `trace_ptraceR_comp`). It is linear, preserves positivity and the trace (`ptrace_add`, `ptrace_smul`, `ptrace_isPositive`, `trace_ptrace`), and sends |x⊗y⟩⟨x'⊗y'| to ⟨y', y⟩|x⟩⟨x'| (`ptrace_rankOne_tensor`). With these, `PFUL.Countable.valid_density_l2` restates validity on countable alphabets in trace form. For every density operator ρ on ℓ²(sources × input ancillas), entangled ancillas included, the output ΦρΦ† of the unitary from `induced_unitary_l2` and the sink state Tr_Y(ΦρΦ†) are density operators, so Tr = 1. The Choi form Tr[W(M_A ⊗ M_B ⊗ …)] = 1 is also formalised for countable alphabets (`lean/PFUL/BornPairing.lean`). There neither W nor a local Choi operator is trace class (a channel's Choi operator has partial trace equal to the identity), so the pairing is not a trace of a product of trace-class operators. Instead W = |U⟩⟩⟨⟨U| is kept as the family of its row vectors u_r, with entries u_r(c) = conj M(r, c) and M(r, c) = ∏_k V_k(…) (`rowVec_apply`). The pairing with an input density operator ρ is the series Σ_r ⟨u_r, ρ u_r⟩ over sink outcomes r = (o, y), which is the limit of its finite truncations; in finite dimensions it is exactly the Born rule Tr[W(ρ ⊗ 1 ⊗ ⨂ C_k)ᵀ] (`PFUL.Choi.born_eq_trace`). `PFUL.Countable.valid_born_l2` proves that this series has nonnegative terms, converges unconditionally to 1, and equals Tr[Tr_Y(ΦρΦ†)] from `valid_density_l2`. `PFUL.Countable.valid_kraus_l2` (`lean/PFUL/KrausL2.lean`) extends this to arbitrary local channels with countably many Kraus operators: V_k(o, y)(i, x) = ⟨o|K_y|i, x⟩ with the Kraus index y as output ancilla, so completeness Σ_y K_y†K_y = 1 is orthonormality of the columns of V_k (an isometry, not a unitary). The induced operator is then an isometry (`induced_isometry_l2`); its columns are orthonormal by a polarization argument that reduces the Gram identity to the unit-column theorem (`induced_gram`). For every density operator ρ, ΦρΦ† and Tr_Y(ΦρΦ†) are density operators, and the Born pairing converges to 1. The polar decomposition is formalised for every bounded operator (`lean/PFUL/Polar.lean`). With |T| = √(T†T) (Mathlib's continuous functional calculus), there is a partial isometry V, isometric on the closure of the range of |T| and zero on its orthogonal complement, with T = V|T|, V†V the projection onto that closure, and V†T = |T| (`PFUL.Polar.polar`, `adjoint_partialIso_comp`, `adjoint_partialIso_comp_self`). For trace-class T, |T| is trace class and ‖T‖₁ = Tr|T| (`absOp_mem`, `traceNorm_eq_trace_abs`). Conversely, T is trace class iff Σ_i ⟨e_i, |T| e_i⟩ converges in some Hilbert basis (`mem_traceClass_iff`). V is a partial isometry, VV†V = V (`IsPartialIsometry`, `isPartialIsometry_partialIso`). The decomposition is unique: if T = WA with A positive, W isometric on the range of A and zero on its orthogonal complement, then A = |T| and W = V (`polar_unique`). A self-contained, Mathlib-style version of the polar decomposition, with no project dependencies, is in `lean/MathlibPR/PolarDecomposition.lean`. The trace-class files are universe-polymorphic: a Hilbert space H may live in any universe `Type u`, with Hilbert-Schmidt factors and basis index types in the same universe. The countable-alphabet theorems (`valid_density_l2`, `valid_born_l2`, `valid_kraus_l2`) are universe-polymorphic too, as are the finite-alphabet combinatorial files. Trace-class operators are compact (`PFUL.TraceClass.isCompactOperator_of_mem`, via Hilbert-Schmidt operators as norm limits of finite-rank truncations), and every trace-class T has a Schmidt decomposition (`PFUL.Polar.schmidt`): a Hilbert basis v of eigenvectors of |T| with eigenvalues s_n ≥ 0, vectors u_n orthonormal where s_n ≠ 0, T x = Σ s_n⟨v_n, x⟩u_n, and Σ s_n = Tr|T| = ‖T‖₁. For a local channel given by its Kraus kernel, the Choi kernel J(o,a;o',a') = Σ_y V(o,y)(a) conj V(o',y)(a') converges, satisfies the trace-preservation condition Σ_o J(o,a;o,a') = δ_{aa'}, and is positive semidefinite on every finite section (`PFUL.Countable.choiKernel_tp`, `choiKernel_psd`, `lean/PFUL/ChoiL2.lean`). Conversely, every kernel on countable alphabets whose finite sections are positive semidefinite and which satisfies the trace-preservation condition is the Choi kernel of a Kraus kernel over a countable Kraus index with Σ_y K_y†K_y = 1, so `valid_kraus_l2` applies to every such Choi-specified channel (`PFUL.Countable.exists_kraus_of_choi`, `lean/PFUL/ChoiConverse.lean`; Mathlib's Moore–Aronszajn reproducing-kernel Hilbert space, then Gram–Schmidt over an enumeration). `PFUL.TraceClass.IsCPTP` is a standalone predicate for maps on trace-class operators: they preserve the trace class, are linear there, preserve the trace, and Φ ⊗ id_Z preserves positivity for every finite ancilla Z. Every Stinespring/Kraus channel ρ ↦ Tr_J(VρV†), with V an isometry and J any Kraus index, satisfies it (`isCPTP_stinespring`, `lean/PFUL/CPTP.lean`), and CPTP maps send density operators to density operators (`IsCPTP.isDensity`). Finite-rank operators are dense in the trace class in trace norm (`PFUL.TraceClass.exists_finiteRank_traceNorm_lt`). `IsNormalCPTP` adds trace-norm boundedness (continuity) to `IsCPTP`, and on countable ℓ² a map is normal CPTP iff it is a Kraus channel ρ ↦ Tr_Y(UρU†) over a countable Kraus index (`PFUL.Countable.isNormalCPTP_iff_kraus`, `lean/PFUL/KrausNormal.lean`). The proof takes the Choi kernel of the map (positive by complete positivity, trace preserving), factors it by `exists_kraus_of_choi`, and extends agreement from the matrix units |a⟩⟨a'| to the whole trace class by trace-norm continuity (`eq_of_rankOne_basis`). The kernel-form channel of `valid_kraus_l2` is identified with the abstract Stinespring channel (`krausChannel_eq_stinespring`), so validity holds for arbitrary normal CPTP local channels on countable alphabets (`PFUL.Countable.valid_normalCPTP_l2`). For the commuting Switchboard case of H.8.4, the linear-algebra core is formalised in finite dimensions (`PFUL.Switchboard.commuting_blend`): if the rank-one projectors commute with those of a reference orthonormal basis, p_φ is a convex mixture of deterministic records, one per basis vector. That each record is a process function is not formalised. The Schmidt series also converges in trace norm, with ‖T − Σ_{n∈F} s_n|u_n⟩⟨v_n|‖₁ ≤ Σ_{n∉F} s_n (`PFUL.Polar.schmidt_traceNorm`). The H.12 counterexample is formalised in finite dimensions (`PFUL.Counterexample.purification_conjecture_false`): the Switchboard is pure against all finite local ancillas and unitaries (`isPure_Vsb`), its induced process is valid under all stochastic local interventions (`valid_pcl`), and it violates an inequality satisfied by every process function on three binary parties, L(p) = (32 − 24√2)/128 < 0, so it lies outside their convex hull; the finite checks are kernel-evaluated by `decide +kernel` without `native_decide`. The counterexample's own definitions are linked to the general framework: its process-function predicate is exactly `PFUL.Countable.IsProcessFunction` of the bit-string form (`PFUL.Counterexample.isPF_iff`), every point of the process-function hull is valid by the general column identity (`valid_pfPoint`, `valid_of_mem_convexHull`), and the theorem is restated with the general definition (`purification_conjecture_false'`). Infinite-dimensional ancillas are covered in Lean: the loop is unitary against ancillas of any cardinality and against local operations given only as unitary kernels, with no boundedness assumed (`PFUL.Counterexample.isUnitaryKer_Vsb`, `isUnitaryAll_Vsb`, `purification_conjecture_false_unitaryKer`; Round 11). For continuous alphabets the combinatorial core of F.5 is formalised (`PFUL.Continuous.tau_bijective`, `fiber_const`, `tauInv_apply`, `c_indep`, any cardinality), and so is the measure-theoretic step: for finitely many parties with standard Borel abelian groups carrying σ-finite right-invariant measures (Haar measure, Lebesgue measure on ℝ, the circle, counting measure), τ is measure preserving for every measurable process function, causal or not (`PFUL.Continuous.tau_measurePreserving`, with `tau_measurePreserving_real` and `tau_measurePreserving_circle`; `lean/PFUL/ContinuousMeasure.lean`). Its inverse is Borel (`tauInv_measurable`, Lusin–Souslin). The closed loop (Uψ)(o) = φ(o)ψ(o − w(o)) with any measurable unit-modulus phase φ is a unitary of L² (`PFUL.Continuous.closedLoop_unitary`, built from a Koopman unitary and a phase unitary; `lean/PFUL/ContinuousUnitary.lean`). The counterexample's purity is tied to the process-matrix form: `compose V A` depends on V only through its Choi vector |V⟩⟩, and the Switchboard's W = |Vsb⟩⟩⟨⟨Vsb| is Hermitian with W² = (Tr W)W (`PFUL.Counterexample.compose_eq_link`, `compose_congr_choiVec`, `Vsb_pure_choi`; `lean/PFUL/ChoiLink.lean`).

## Appendix B. Unequal input and output alphabets

Nothing in Section 1 needs |I_k| = |O_k|.

- U : O (x) P -> I (x) F, with P = prod I_k and F = prod O_k, maps |o,e> to |w(o)+e, o>. Both sides have dimension prod |I_k||O_k|, and U is a permutation of basis states, so U is unitary for every w. Only I_k needs a group structure (Z_{|I_k|}); O_k is an arbitrary finite set.
- The exclusivity Lemma and its proof never compare I_k with O_k.
- A party with |I_k| != |O_k| cannot apply a unitary I_k -> O_k. Its most general deterministic operation is a CPTP map, or a unitary with ancillas, I_k X_k -> O_k Y_k with |I_k||X_k| = |O_k||Y_k|. The Theorem is stated in exactly that generality (and so is the Lean theorem, whose local types I k, O k, X k, Y k are independent). The Gram computation gives M M^dagger = 1, and M is square because dim(P X) = prod |I_k||X_k| = prod |O_k||Y_k| = dim(F Y). Appendix A then applies verbatim.

**What holds.** For any finite input and output alphabets, with any sizes, the permutation lift of a process function is a pure and valid process. **What is not covered here.** Infinite alphabets (countable ones are treated in Appendix F; continuous ones remain open, and Baumeler et al. 2019 also treat continuous variables), and lifts built from a different bijection than U.

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

**C.3 Purifiable set and the (former) conjecture.** The control-register argument of C.1 works for any purifiable processes, not just process functions. So the purifiable classical processes form a convex set containing the hull of the process functions. We conjecture they are exactly that hull:

*Conjecture (refuted, H.12.1).* A classical process is purifiable iff it is a mixture of process functions. The "if" half is C.1; the "only if" half is false.

*Provenance.* The "if" half was asserted earlier by Baumeler, Gilani and Rashid (Quantum 6, 673 (2022), ref. 27): every mixture of process functions embeds into a reversible process function, and is therefore "unitarily extensible". As far as we found, the "only if" half had not been stated in print before this note, and no counterexample was known. A related open question is Kunjwal and Oreshkov's (arXiv:2307.02565, ref. 36): can correlations from unitarily extendible process matrices be antinomic? The refutation here does not settle it; see H.13.5.

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
- Interpretation [superseded by H.12]: this is consistent with the conjecture that none of the 49 non-deterministic vertex orbits is purifiable. But a local search can miss solutions, so it is not a proof. Only orbits 7 and 50 (C.2) have exact certificates.

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

**C.6 Degree-4 certificates for orbit 8 (Oct 22 2026) [numerical obstruction; no certificate; no paid compute used].** C.5 proposed a degree-4 Positivstellensatz: exhibit a subspace L of V_W of dimension 67 that contains no nonzero jointly isotropic vector. That would rule out an isotropic 16-plane, since 16 + 67 > 82. The degree-2 (form-based) version provably fails (C.5). Before renting hardware I tested whether any certificate of this shape can exist.
- *Radical.* The common radical of the 4096 constraint forms (as sesquilinear forms on V_W, orbit 8) has dimension exactly 1 (c0; smallest singular values 0.81, 0.81, 2e-14). So work in R^perp (dim 81). (cert/cone67c.py)
- *Probe.* For Haar-random L in R^perp, minimise the isotropy loss f(u) = ||L3perp(X(u) Lam X(u)^H)||^2 over unit u in L (Adam, then L-BFGS). The baseline for random unit u is min 0.078, median 0.108.
  - d = 67: minimum 1.9e-9 (cone67c_orbit8.log). An earlier run without removing the radical gave 1.3e-8 (cone67b_orbit8.log).
  - d = 60: minimum 2.3e-7 (cone60c_orbit8.log).
- *Reading [numerical].* The loss falls 7-8 orders of magnitude below baseline. So random subspaces of dimension 67, and even 60, contain (numerically) jointly isotropic vectors outside the radical. A certificate "L has no isotropic vector" of any degree cannot exist for such an L, because it would be a proof of a false statement. The set of isotropic directions is large: it meets random subspaces of codimension at least 21 in R^perp. This matches H.2, which found tangent dimension about 27-31 on the cone. The forms are real quadratic (sesquilinear), so the complex projective dimension theorem does not apply, and I have not proved that *every* 67-dim L meets the cone. A specially chosen L is not excluded by this probe. But no construction of one is known, and random choice fails.
- *The remaining degree-4 route is out of reach by size.* Level-2 Lasserre on the full frame problem (16 x 82 complex, i.e. 2,624 real unknowns) has a moment matrix indexed by monomials of degree <= 2: about 3.4 x 10^6 rows. That is far beyond any $60 machine. Quotienting by the U(16) frame symmetry leads to the projector relaxation of Appendix E (degree 2 in P = degree 4 in the frame). That relaxation is already feasible for E_ex1, so it is weaker than single-form inertia and cannot certify orbit 8.
- *Spend.* Because both degree-4 formulations are ruled out (one numerically, one by size and by the E_ex1 control), no instance was rented. **Paid compute used: $0.** Existing vast.ai CLI credentials were found on the box and left untouched. **No certificate for orbit 8. Status unchanged: [numerical only].**


*Proof idea for "only if" (not completed).* A purification U restricted to classical permutation instruments gives a unitary M for every reversible local classical operation. One would like to show that M's action on basis states then decomposes into permutations, giving a deterministic decomposition. We have not proved this. E_ex1 shows the classical consistency of W alone is not enough.

**Answer.** Not every classical process admits a unitary extension: E_ex1 (and one other vertex orbit) provably does not. Mixtures of process functions do. Whether those are the only ones was the conjecture above; H.12.1 shows they are not.

## Appendix D. Purifications of classical processes: the physics route
Status labels: **[proved]**, **[conjecture]**, **[gap]**. Nothing here proves the conjecture. (Written before H.12, which refutes it.)

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
orthogonal to |psi>. Any proof of the conjecture would have had to use those states (moot after H.12). This is where proposal (2) breaks down:
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
through a source-label decomposition. Status at the time: the conjecture was open; D.3 is refuted. The conjecture itself was later refuted
(H.12.1).

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
is the source-sink construction with a random source. Hence **the conjecture was equivalent to: a classical process
that is quantum-purifiable is already classically purifiable.** D.4 shows the quantum purification itself need not be
classical (its labels are contextual), so this has to be argued at the level of W.

**Facets of the PF hull [computation].** The 744 process functions (3 parties, binary) span a 37-dimensional affine
space. Facet enumeration results are recorded below. Each facet that some open orbit violates is a candidate
inequality that purifiability would have to imply.
Full facet enumeration was not done: pycddlib does not build on the box, and 744 vertices in dimension 37 may have
very many facets. Instead, sep.py finds by LP a separating inequality of the PF hull (box-normalised, |f| <= 1):
E_ex1 and orbit 7 violate one by 6.0, orbit 8 by 4.0, and a PF mixture by 0, as expected. These inequalities are not
reduced modulo the affine hull or by symmetry, so their supports carry no meaning yet. **No inequality has been
derived from purifiability. The conjecture remained open at this point; H.12.1 later refuted it.** Next steps: enumerate facets with lrs/normaliz or by
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
t = 0.2 (60.1); the same code reaches about 1e-13 on Lugano itself. This was read as consistent with the conjecture [superseded by H.12], since the
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

**Algebraic geometry (assessed, infeasible by size).** Solving the Theorem 4 system directly (real quadratic, since the forms are sesquilinear) means 352 real unknowns and 23,552 equations for E_ex1, and about 2,112 unknowns and 100,352 equations for orbit 8. Total-degree homotopy continuation would track about 2^352 and 2^2112 paths, and proving that no solution exists is the hard case. Gröbner bases are far out of reach. Symmetry does not reduce the unknowns, and sub-problems with small r are uninformative because non-existence first appears near r = 15-16 (code/stochastic/alggeom/SIZE_ESTIMATES.md).

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

**F.5 Continuous alphabets (Oct 23 2026) [definitions; proved; open where marked].**

*Setting.* Finitely many parties. Each I_k = O_k = G_k is a second-countable locally compact abelian group (R, the circle U(1), R^d, or any countable group) with Haar measure λ_k. These are standard Borel spaces and λ_k is σ-finite. Write G = ∏ G_k and λ = ⊗ λ_k.

*Definition F.5.1 (measurable process function).* A Borel map w : G → G is a measurable process function if, for every family of Borel maps f_k : G_k → G_k, the map o ↦ f(w(o)) has exactly one fixed point. (Every argument below uses only translations, constant maps and two-valued maps, which are Borel. So this is equivalent to asking the same for all maps f_k, measurable or not.)

*Three candidate definitions of "the closed loop", compared.*
- (a) **Point maps.** Restrict the local operations to unitaries that act on points: V ψ(o) = u(o) ψ(g(o)), with g : O_k → I_k a Borel bijection with Borel inverse that is non-singular (preserves null sets), and |u|² = d(λ∘g)/dλ. By the classical theorem that automorphisms of L^∞ of a standard measure space come from non-singular point maps (not re-proved here), these are exactly the unitaries that carry multiplication operators to multiplication operators. They are the continuous analogue of monomial (phase × permutation) matrices, and include translations, phase multiplications (momentum kicks), reflections, squeezes ψ(o) ↦ √a ψ(ao), and any measurable rearrangement. For them the kernel V(o,i) = u(o) δ(i − g(o)) can be evaluated on the graph i = w(o)+e, and the countable formula M(o,e) = ∏_k V_k(o_k, w_k(o)+e_k) becomes the operator (Mψ)(o) = u(o) ψ(t(o)), where t(o) = g(o) − w(o). This is canonical: no choice is made.
- (b) **Direct integrals / disintegration.** One writes L²(G) = ∫^⊕ ℂ dλ and asks V_k to be decomposable. Decomposable unitaries are multiplication operators, which are the special case g = id of (a). A general V_k does not respect the fibres, so the disintegration does not define M; the useful content of (b) is contained in (a).
- (c) **Limits of discretisations.** Take M = lim M_n along refining finite partitions, using F.3 for each M_n. Every M_n is unitary, but we found neither a proof that the limit exists nor a proof that it is independent of the partitions for general V_k. Without that, (c) is not yet a definition.
- (d) **Circuits, for causal w.** When w is causally ordered, close the loop as a circuit. Apply the first party's V, then a controlled translation C = ∫^⊕ |o⟩⟨o| ⊗ T_{w_k(o)} dλ(o) (a direct integral of unitaries, hence unitary), then the next party, and so on. This works for **all** local unitaries and ancillas.

*Choice.* We adopt (a) for general measurable process functions and (d) as its extension to all local unitaries when w is causal. They agree where both apply (both reduce to the same composition of point maps), and both reduce to the matrix formula of F.2 when every G_k is countable with counting measure. Option (a) is the largest class on which the defining formula of F.2 makes sense without choices, because it needs the kernel of V_k on a null set (a graph). Option (c) remains a programme.

*Lemma F.5.2 [proved; Lean, any cardinality: `PFUL.Continuous.tau_bijective`, `fiber_const`, `tauInv_apply`, `c_indep`].* Let w be a process function on groups G_k (no measure needed) and τ(o) := o − w(o).
(i) τ is a bijection. Its inverse sends a source value e to the fixed point for local translations i ↦ i + e_k.
(ii) If τ(o) and τ(o') agree at every party other than a, then w_a(o) = w_a(o').
(iii) Hence τ^{-1}(e)_a = e_a + c_a(e_{−a}), with an offset c_a that does not depend on e_a.
Proof of (ii): otherwise take f_a(x) = o_a if x = w_a(o) and o'_a otherwise, and f_k(i) = i + τ(o)_k for k ≠ a. Then o and o' are two distinct fixed points.

*Theorem F.5.3 [proved, paper; Lean: `PFUL.Continuous.tau_measurePreserving`] (measure preservation, causal or not).* For every measurable process function w, τ is a measure-preserving Borel automorphism of (G, λ).
Proof, by induction on the number n of parties.
- n = 1: by (ii), w is constant, so τ is a translation.
- n > 1: fix a party a. For each value x of o_a, the function w_{−a}(x, ·) is a process function on the other n−1 parties (set f_a ≡ x). So by induction τ^x(o') := o' − w_{−a}(x, o') is a measure-preserving bijection of G_{−a}, and τ(o)_{−a} = τ^{o_a}(o_{−a}).
- Let σ(o) = (o_a, τ(o)_{−a}). σ is a Borel bijection, so its inverse is Borel (Lusin–Souslin). σ preserves λ by Tonelli: λ(σ^{−1}B) = ∫ λ_{−a}((τ^x)^{−1}B_x) dλ_a(x) = ∫ λ_{−a}(B_x) dλ_a(x) = λ(B).
- τ∘σ^{−1}(x, e') = (x − w_a(σ^{−1}(x,e')), e'). By (ii), w_a is constant on each set {τ(o)_{−a} = e'}. So τ∘σ^{−1}(x, e') = (x − c_a(e'), e') with c_a Borel, a fibrewise translation, which preserves λ by Tonelli and the translation invariance of Haar measure.
- Hence τ = (τ∘σ^{−1})∘σ preserves λ. ∎
*Lean.* `tau_measurePreserving` proves F.5.3 for finitely many parties, each G_k a standard Borel abelian group (MeasurableAdd, MeasurableSub₂) with a σ-finite right-invariant measure μ_k, and λ = ∏ μ_k. Corollaries cover ℝ with Lebesgue measure (`tau_measurePreserving_real`) and the circle ℝ/Tℤ (`tau_measurePreserving_circle`). The Lean proof follows the paper: split off party a with `MeasurableEquiv.piEquivPiSubtypeProd`, apply the induction hypothesis to the reduced process inside a skew product (`MeasurePreserving.skew_product`, which is Tonelli), then apply the shear (x, e') ↦ (x − c(e'), e'), whose offset is independent of x by `fiber_const`. The Borel inverse comes from `Measurable.measurableEmbedding` (Lusin–Souslin).
This is the measure-theoretic replacement for the countable "expected number of fixed points = 1" identity: (ii) says that the fixed-point count is forced to 1 one party at a time, and Tonelli integrates the parties out in turn.

*Corollary F.5.4 [proved, paper] (measure-preserving local bijections; the earlier open case).* Let the local operations be measure-preserving Borel bijections f_k (with Borel inverses g_k = f_k^{−1}). Then the closed-loop map e ↦ s(e) (the unique fixed point of o ↦ f(w(o)+e)) preserves measure, in the causal and the non-causal case alike.
Proof: s^{−1}(o) = g(o) − w(o) = τ_{w'}(g(o)) with w' = w∘g^{−1}. Relabelling outputs locally preserves the process-function property, so w' is a measurable process function. Then apply F.5.3. ∎

*Theorem F.5.5 [proved, paper] (unitarity in class (a)).* For every measurable process function w and every family of point-map unitaries V_k ∈ (a) (with or without point-map ancillas; append the ancilla coordinates as extra groups on which w does not act), the closed-loop operator (Mψ)(o) = u(o) ψ(g(o) − w(o)) is unitary on L²(G). Proof: ∫ |u(o)|² |ψ(τ_{w'}(g(o)))|² dλ(o) = ∫ |ψ(τ_{w'}(x))|² dλ(x) = ‖ψ‖². The first step is the change of variables x = g(o), using |u|² = Jacobian of g; the second is F.5.3. M is surjective, with inverse ψ ↦ (ψ / u)∘t^{−1}. ∎

*Lean, Round 11 [PROVED, Lean].* Multiplication by √ρ is an isometry L²(ρλ) → L²(λ) for every measurable ρ ≥ 0, zeros allowed (`PFUL.Continuous.densityIsoₗᵢ`). Hence, for every measurable map g with g_*(ρλ) = λ (not assumed injective), ψ ↦ φ·√ρ·(ψ∘g) is an isometry (`closedLoop_isometry`), and it is unitary when g is a Borel bijection and ρ ≠ 0 only almost everywhere (`closedLoop_unitary_ae`). In Jacobian form, on a finite-dimensional real space with Haar measure: if g is measurable, injective and differentiable (within s) on a conull Borel set s whose image is conull, then ψ ↦ φ·√|det g'|·(ψ∘g) is an isometry, even if det g' vanishes on a set of positive measure (`closedLoop_jacobian_isometry`). If g is moreover a Borel bijection with det g' ≠ 0 almost everywhere, it is unitary (`closedLoop_jacobian_unitary_ae`). This covers piecewise-smooth bijections such as the threshold lifts of the Lugano function, which are not differentiable on the cell boundaries. Two remarks [PROVED, paper]. (i) If det g' = 0 on a set Z of positive measure, the isometry is not onto, since every vector in its range vanishes a.e. on Z; so "unitary ⟺ det g' ≠ 0 a.e." in this setting. (ii) The conull-image hypothesis (Lusin's property (N) for the exceptional set) cannot be dropped: an increasing singular homeomorphism of [0,1] (for example the inverse of Minkowski's question-mark function) is differentiable a.e. with derivative 0 a.e. and carries a null set onto a conull set. "Local diffeomorphism" is read here as a bijection that is a diffeomorphism off a null set. A local diffeomorphism that is not injective (a k-fold cover) gives ‖Mψ‖² = Σ over preimages, so M is not an isometry; such maps are not point-map unitaries and are outside (a).
*Lean (translation class with phases).* `PFUL.Continuous.closedLoop_unitary`: for every measurable process function w and every measurable φ with |φ| = 1, there is a linear isometric equivalence U of L²(∏ G_k, ∏ μ_k) with (Uψ)(o) = φ(o)ψ(o − w(o)) almost everywhere. This is the case g = id, u = φ (pure translations decorated with phases). General point maps g with a Jacobian factor are not in Lean; they reduce to this case by the change of variables x = g(o).
Thus the open lift U is unitary (F.1, measure-preserving), and every induced map is unitary for point-map local operations, for every measurable process function.

*Theorem F.5.6 [proved, paper] (causal w, all local unitaries).* With definition (d), M is a product of unitaries, so it is unitary for all local unitaries and ancillas.

*Open (non-causal w, general local unitaries).* For a non-causal measurable process function (for example the Lugano function lifted to R³ by threshold sets, which is a measurable process function with piecewise-translation τ) and local unitaries outside class (a), such as a Fourier transform, we have no canonical definition of the closed loop. Here is why. A non-causal w admits no circuit (d): circuits are causally ordered, and the Lugano statistics violate a causal inequality. And the formula of (a) needs the kernel of V_k on a null set. *Conjecture F.5.7:* for every measurable process function and all local unitaries, the discretisations of (c) converge strongly to a unitary that is independent of the partitions and extends (a) and (d). Supporting evidence (heuristic, not a proof): every discretisation is unitary (F.3), and the limit exists in the two classes where we can compute it, (a) and (d).

*Proposition F.5.8 [PROVED, paper] (F.5.7 for causal w).* Fix countable partitions P_n of each G_k into cells (for ℝ, the grids h_nℤ + [0, h_n) with h_n → 0 along a refining sequence), let E_n be the conditional expectation onto the step functions of P_n (so E_n → 1 strongly), and let V_{k,n} be unitaries of E_n L² with V_{k,n}E_n → V_k and V_{k,n}*E_n → V_k* strongly. Let w_n be cell-valued process functions, causal in the same order as w, with w_n → w λ-a.e. Then the discretised closed loops M_n E_n (F.3) converge strongly to the circuit closed loop M_(d) of (d). In particular the limit exists and does not depend on the partitions or on the approximating V_{k,n}, w_n.
Proof. For causal w_n the matrix formula of F.2 equals the circuit product (apply V_{1,n}, then the controlled translation C_n by w_{1,n}, then V_{2,n}, …); this is the countable case of F.5.6. A product of a fixed number of uniformly bounded, strongly convergent sequences converges strongly to the product of the limits. So it suffices that C_n → C strongly, where (Cψ)(o, x) = ψ(o, x − w_k(o)). For ψ ∈ C_c, ‖(C_n − C)ψ‖² = ∫ ‖T_{w_{k,n}(o)}ψ(o,·) − T_{w_k(o)}ψ(o,·)‖² dλ(o). The integrand tends to 0 pointwise by strong continuity of translation and is bounded by 4‖ψ(o,·)‖², so dominated convergence applies. C_c is dense and ‖C_n‖ = 1, so C_n → C strongly. ∎
*Consequence.* F.5.7 holds for causal w with any discretisation scheme of this kind, and the limit equals (d). For a Fourier-type V_k (the Fourier transform on L²(ℝ), or on a compact group) the proposition applies as soon as unitary grid approximants V_{k,n} with V_{k,n}E_n → V_k and V_{k,n}*E_n → V_k* strongly are fixed. We did not verify that a particular scheme (for example centred, rescaled discrete Fourier transforms) has this property, so for Fourier-type local unitaries with causal w the conclusion is conditional on that approximation step [PROVED modulo the approximation hypothesis; not in Lean]. For non-causal w, F.5.7 remains **OPEN**. The argument above fails at its first step: a non-causal w_n has no circuit form, so M_n is not a fixed-length product of strongly convergent factors, and the F.3 unitaries M_n are not known to have uniformly convergent matrix entries. We found no counterexample either.

**Status.** Proved (paper and Lean, finite and countable), for countable alphabets with a group structure on the inputs and finitely many parties: the lift is unitary under all local unitaries with ancillas (F.1-F.3). Continuous alphabets (F.5): definitions F.5.1 and (a)/(d) adopted. Measure preservation of the closed loop for every measurable process function, causal or not (F.5.3), and the measure-preserving-bijection case (F.5.4), are proved in the paper. Unitarity holds for point-map local unitaries (F.5.5), and for all local unitaries when w is causal (F.5.6). The combinatorial core (F.5.2) is machine-checked. F.5.3 is now machine-checked (`PFUL.Continuous.tau_measurePreserving`), as is F.5.5 for translations with phases (`closedLoop_unitary`). F.5.5 for general point maps is machine-checked (Round 10: `closedLoop_general_unitary`, `closedLoop_jacobian_unitary`; Round 11: a.e.-smooth bijections with a.e.-nonzero Jacobian, `closedLoop_jacobian_unitary_ae`, and an isometry with degenerate Jacobians, `closedLoop_jacobian_isometry`). Conjecture F.5.7 holds for causal w (Proposition F.5.8, paper). Open: a canonical closed loop for non-causal w with general local unitaries such as a Fourier transform (Conjecture F.5.7 in the non-causal case).

## Appendix G. Two parties: purifiable = PF blend, trivially (Oct 21 2026)

**Theorem G.1 [proved].** Let p(a,b|x,y) be a valid classical process on two parties A, B, with finite alphabets of any sizes: a, b are the inputs and x, y the outputs. Valid means p >= 0 and sum_{a,b} p(a,b|f(a),g(b)) = 1 for all functions f, g. Then p is a convex combination of deterministic causally ordered process functions. Each of these has one of two forms: a = a0 constant and b = h(x), or b = b0 constant and a = h(y).

**Corollary G.2 [proved].** For two parties, the former purification conjecture of Section 9 holds (in contrast with three parties, H.12.1). Both sides are true for every valid classical process. Every such process is a mixture of process functions (G.1), so it is purifiable (C.1). Also, every bipartite process function is causally ordered: a 0/1 point that is a convex combination of 0/1 points equals one of them. So the two-party case says nothing about the open multipartite question. The separation between "classically consistent" and "reversibly realisable" starts at three parties, where E_ex1 lives.

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

Status labels: **[proved]**, **[numerical]**, **[cited]**, **[failed]**. The three-party conjecture was open when this appendix was written; H.12.1 refutes it. Code: code/stochastic/structural/.

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

**Does purifiability add anything here?** On the classes of H.1 and H.2, no: every valid process is already a PF mixture. The natural next statement would be "purifiable and marginally first imply valid conditionals". It would settle the conjecture for the 19 marginally-first orbits, including orbit 8. It is open [not proved]; H.5 shows the W-level version fails. D.2 and D.8 show it cannot follow from the source sector alone.

### H.2 Route B: a determinantal bound for orbit 8 [failed, numerical]

Idea. If S is a jointly isotropic subspace (AFNB Thm 4, reduced as in C.2) and u is in S, then S lies in ker K(u), where K(u)_{t,b} = Q_t(u, e_b) runs over the 196 linearly independent constraint forms of orbit 8 (m = dim V_W = 82). So dim S <= dim R + (82 - rank K(u)) for any isotropic u outside the common radical R (dim R = 1, spanned by c0). An exact proof would need rank K(u) >= 67 on the whole isotropic cone outside R. That is one determinantal variety (67-minors) with no real point on the cone, which can be checked algebraically in principle.

Probe (detprobe.py). Generic near-isotropic u (residual ~1e-7 to 1e-6) have numerical rank 81. But minimising the tail singular values of K(u) along the cone gives points whose spectrum drops from 1.6e-2 (sigma_50) to 3.4e-4 (sigma_55) and stays there down to sigma_66, with isotropy residual 2.5e-7. So, numerically, the cone contains u with rank K(u) of about 51-55. The single-vector bound then gives only dim S <= ~28-32, not < 16. The determinantal route with one vector cannot work for orbit 8. A flag version (rank conditions on pairs u, v in S) would be needed, and it is a much larger variety. Not attempted. Gröbner bases on a symmetric ansatz were not attempted, because the stabiliser of orbit 8 has order 8 (App. E), too small to reduce the 82 complex unknowns per basis vector to a tractable size. **No exact proof for orbit 8.**

### H.3 Route C: counterexample hunt from the unitary side [numerical, negative]

Parametrisation (hunt.py). U = U0 exp(iH) is a 64 x 64 unitary O (x) P -> I (x) F, with P = F = C^8 and source |0>. The loss is a purity residual sum ||M M^dagger - 1||^2 over random Haar local unitaries, with and without qubit ancillas, plus a penalty on the off-diagonal part of W (classicality), minus the value of a PF-hull facet from orbit 82 (D.7) under a random symmetry. A point with purity residual ~0, W diagonal and facet > 0 would be a purifiable process outside conv(PF).
- Random start (U0 = 1, 8 seeds x 20,000 Adam steps): purity was never reached. The final residual (20 fresh samples, qubit ancillas) was 10-172. The facet values there are meaningless, because W is not normalised. **[failed: the optimiser does not even find pure unitaries from random starts]**
- Start at the Lugano lift (exactly pure, facet image chosen tight = 0 at Lugano; 8 seeds): the search trades purity against violation. Final facet violation was 0.008-0.018 at purity residual 0.13-2.4 (ancilla samples) and off-diagonal mass 4e-5 to 7e-4. Not one run kept both residuals near 0 with positive violation.

This was read as consistent with the conjecture [superseded by H.12]: leaving the hull at a Lugano vertex costs purity at once, as in D.8's boundary test. It is local, small-sample evidence, not a proof. No counterexample was found.

### H.4 Summary
- Proved: H.1 (some party last implies PF mixture) and H.2 (classically causally separable implies mixture of causally ordered PFs). On both classes every valid process is a PF blend, so no gap can occur there. Also proved: marginal "firstness" does not reduce (E_ex1).
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

**What this leaves open.** The conjecture was thereby reduced to purifications in which **every** party has a parent among the party outputs, i.e. every party's input is influenced by some output in V. Lugano-type lifts are like this: their causal graph is a 3-cycle. Theorem H.6.2 says nothing about a W whose only purifications are of this kind. That is the same class flagged as open in Section 9, now characterised at the operator level. A purifiable non-blend, if one exists, must be such a W: one with no first party and no last party in any purification. W-level lastness already gives H.1. Operator-level lastness is a stronger hypothesis, so it is covered too.

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

### H.7 Purifications with no operator-first party: a search beyond Lugano (Oct 22 2026) [numerical; two small proved statements]

**Goal.** By H.6, a purifiable process outside conv(PF) can only have purifications in which no party is operator-first. This section looks for such purifications with three binary parties and small source and sink, and asks whether any of them induces a classical process outside the hull. **No non-blend was found.** Code is in code/stochastic/cyclic/, with logs and .npy results there.

**Tests applied to every purification found.**
- *Purity:* max ||M M^dag - 1|| under fresh Haar local unitaries, with and without qubit ancillas.
- *Operator-first residual for each party:* the channel P (x) O -> I_k must be independent of O (common.opfirst).
- *Causal graph:* pairwise influence O_j -> I_k through V (common.influence; an edge is drawn when the residual is > 1e-6).
- *Induced classical process:* p(i|o).
- *Hull test:* L1 distance to conv(744 PFs) by LP.
- *Lugano weight:* the minimal weight on the 64 Lugano-orbit PFs in any PF decomposition (LP with L1 slack 1e-7). Weight 0 means p is a blend of PFs that each have a constant component, i.e. classically causally separable (H.2).

**Family A: single-PF lifts and phase variants [proved / numerical].**
- In the lift of Section 1, I_k = w_k(o) + e_k, so party k is operator-first iff w_k is constant.
- Of the 744 binary PFs, exactly 64 have no constant component. They form one orbit under party permutations and bit flips, the Lugano orbit (orbit size 64 = 384/6) [exhaustive check, famA.py].
- So, among single-PF lifts, "no operator-first party" is the same as "Lugano-type".
- Phases: multiplying the lift by a source-only or sink-only phase keeps purity (residual ~2e-15), because these are local unitaries on P or F.
- A generic joint phase exp(i theta(o,e)) destroys purity (residual 0.61-0.68 for three random theta).
- Every pure phase variant induces the same diagonal p, the PF itself.

**Family B: coherent blends of causal orders [proved].** Take the C.1 lift of a blend of three causally ordered PFs whose first parties are A, B and C respectively (PF indices 17, 145, 152 in pfs744.npy).
- In this purification no party is operator-first (residual 0.75 for each party).
- Every output is used, so no party is last.
- Yet W is a blend of causally ordered PFs.
- So "no operator-first party in V" does not imply that W is non-separable, and the structural guess "every purification with no first party is Lugano-like" is **false** as stated.
- The classical analogue (Barrett-Lorenz-Oreshkov 2021) is that cyclic causal structure does not imply causal nonseparability (their classical SWITCH remark).

**Family C: output-dependent source unitaries ("noisy-PF" purifications).** Source P = S (x) T and sink F = O (x) E', with S, T, O, E' each C^8:

    V|o, s, t> = sum_e C_o[e, s] |e>_I |o>_F |e xor t>_F,     C_o in U(8), one per joint output o.

- V is unitary for any choice of the C_o.
- The sink records (o, i), so W is diagonal, with p(i|o) = |C_o[i, 0]|^2.
- Every classical p arises for some C_o; purity is the only constraint.
- The Lugano lift is the case C_o = X^{w(o)}.

**Lemma H.7.1 [proved; numerically verified].** Family C is pure under local unitaries *without ancillas* iff, for all o != o' and all delta in {0,1}^3, with K = C_o C_o'^dag, D = supp(o xor o') and S = D \ supp(delta):

    sum over e_S of (-1)^{|e_S|} K[e, e xor delta] = 0     for every value of e outside S.

*Proof.* Rows (o,t') and (o',t'') of the induced M have inner product sum_e K[e, e xor delta] prod_k U_k[o_k,e_k] conj(U_k[o'_k, e_k xor delta_k]), with delta = t' xor t''. For o = o' this is delta_{delta,0}. For o != o', the factor of party k, as U_k ranges over U(2), spans all of C^2 unless k is in D and delta_k = 0. In that case it spans only (1,-1), because the rows of U_k are orthogonal. The products of these spans give exactly the stated condition. ∎

lemmaC.py confirms the condition numerically:

| C | violation |
|---|---|
| Lugano | 0 |
| random unitaries | 1.58 |
| polished solutions in the table below | 3e-11 to 3.5e-9 |
| rand_12 (polished only to 1.6e-6) | 6.3e-6 |

With ancillas the condition is necessary. It is also sufficient: see H.8.2 (added Oct 22 2026).

**Searches in family C [numerical].** Method: Adam on purity, using sampled local unitaries with and without qubit ancillas (famC.py), then L-BFGS polishing in float64 on a fixed batch of 12 samples (polish.py), then the tests above on fresh samples (characterize.py; charP.json, charP2.json, charL.json).
- Random starts: 11 seeds. 1 failed to become pure (rand_11, polish loss 224). 1 reached only purity 1.6e-6 (rand_12).
- Lugano-seeded starts (noise 0.3): 3 seeds.
- Facet-pushing runs (pure loss minus lambda times a random image of facet 82, lambda = 0.1, 0.3, 1): Lugano-seeded runs reached facet violation 0.89-1.0 only at purity residual 0.03-0.05 (famC_lug_*_{6,8,10}.log). None was pure. This is the same trade-off as H.3. The two random-start facet runs were invalid because of a since-fixed parametrisation bug (a non-Hermitian generator). Their logs were discarded.

| solution | purity | op-first residual A/B/C | causal graph | first or last party at operator level | hull dist | min Lugano weight |
|---|---|---|---|---|---|---|
| rand_1 | 3e-11 | 0 / .52 / .46 | A>B, A>C, B<->C | A first | 0 | 0 |
| rand_2 | 2e-10 | .33 / .53 / .38 | A<->C, A>B, C>B | B last | 0 | 0 |
| rand_3 | 2e-11 | .23 / .22 / .63 | A<->B, A>C, B>C | C last | 0 | 0 |
| rand_12 | 1.6e-6 | .68 / .42 / 0 | A<->B, C>A, C>B | C first | 7e-7 (noise) | n/a |
| rand_13 | 6e-10 | .46 / .24 / 0 | C>A, C>B, B>A | C first, A last | 0 | 0 |
| rand_14 | 5e-10 | .56 / .18 / .30 | B<->C, B>A, C>A | A last | 0 | 0 |
| **rand_15** | 1.4e-10 | .67 / .55 / .73 | **complete (all 6 edges)** | **none** | 0 | **0** |
| rand_16 | 2e-11 | .67 / 0 / .50 | B>A, B>C, A<->C | B first | 0 | 0 |
| rand_17 | 2e-11 | .24 / .44 / .21 | A<->C, A>B, C>B | B last | 0 | 0 |
| rand_18 | 3e-10 | .47 / .48 / 0 | A<->B, C>A, C>B | C first | 0 | 0 |
| **lug_21** | 5e-10 | .75 / .72 / .72 | **complete** | **none** | 0 | **0.93** |
| **lug_22** | 7e-11 | .71 / .72 / .72 | **complete** | **none** | 0 | **0.87** |
| **lug_23** | 7e-11 | .73 / .72 / .74 | **complete** | **none** | 0 | **0.90** |

**Reading [numerical].**
1. Every pure solution found induces a p inside conv(PF), at LP distance 0. **No counterexample.**
2. The rows with an operator-first party are consistent with H.6. An operator-last party (its output influences no input) makes p independent of that output, so H.1 applies. 9 of the 10 random-start pure solutions have a first or a last party.
3. **New: no first and no last party, separable W.** rand_15 is a purification with a complete (maximally cyclic) causal graph, no operator-first and no operator-last party. Its p needs Lugano weight 0, so it is a blend of causally ordered PFs. Together with family B, this shows that the open class "no operator-first party" contains many purifications of causally separable processes.
4. **New: genuinely non-separable continuous family near Lugano.** The Lugano-seeded solutions are pure, are not phased permutations (their C_o are generic unitaries, so not of D.3 form), and have a complete causal graph. Their p needs Lugano weight 0.87-0.93: non-separable, but a PF blend.
5. **Structural guess refuted.** "Every no-first-party purification is Lugano-like up to local unitaries" is false: family B is an exact counterexample, and rand_15 is a numerical one.

*Names.* The gentle version (graded.md, Section 58e) uses informal names: the Ring (the 64 Lugano-orbit single-PF lifts of family A), the Chorus (family B), the Switchboard (family C) and the Shadows (lug_21-23).

**What remained open.** The conjecture on the class (refuted there by H.12.1) of purifications with neither an operator-first nor an operator-last party.
- Within family C, Lemma H.7.1 turns no-ancilla purity into linear conditions on the products C_o C_o'^dag. A proof that these conditions, together with the ancilla conditions, force p into conv(PF) would settle family C. Attempted in H.8: the ancilla conditions are implied (H.8.2), and the hull question is still open.
- Family C has source dimension 64 and records (o, i) in the sink. General purifications can have larger sources and need not have this form (D.4).
- These searches cover a small, structured slice. They are local and few: 13 pure solutions in total.
- **Running jobs:** none. All runs completed or were stopped; the logs are in code/stochastic/cyclic/.

### H.8 The Switchboard lemma: Pauli form, ancillas, and what is and is not forced (Oct 22 2026) [proved parts; hull question numerical]

Task: do the purity conditions of Lemma H.7.1 force the induced p into conv(PF) (37-dim, 744 vertices)? **Answer (at the time): not settled; H.12.1 later answered no.** The conditions are equivalent to full purity, so this is the conjecture restricted to family C (answered negatively by H.12.1). A numerical search (108 runs) found no counterexample, and the trade-off between violation and purity residual is quadratic (Appendix I). What is proved: H.8.1-H.8.5. Code: code/stochastic/cyclic/switchboard/.

Notation. Write U_o := C_o (8x8 unitary, rows indexed by the input string e = (e_A, e_B, e_C)), K_{o,o'} := U_o U_{o'}^dag, and D(o,o') := supp(o xor o'). For a unit source vector phi in S put psi_o := U_o phi. Then p_phi(i|o) = |<i|psi_o>|^2, and psi_o = K_{o,o'} psi_{o'}. The source column s = 0 of H.7 is phi = |0>. The H.7.1 conditions do not mention phi, so every phi gives a purification.

**H.8.1 Pauli form [proved; exact check].** For o != o', the H.7.1 conditions on K = K_{o,o'} hold iff every Pauli coefficient c_{a,b} = Tr[(X^a Z^b)^dag K]/8 vanishes for strings that are non-identity on every party of D. Equivalently,

    K_{o,o'} in A_D := sum over k in D of (1_k (x) L(C^4)),

the linear span (not the union) of the operators that act trivially on at least one party whose output changed.
*Proof.* K[e, e xor delta] = sum_b c_{delta,b} (-1)^{b.(e xor delta)}. On S we have delta_S = 0, and sum over e_k of (-1)^{e_k} (-1)^{b_k e_k} equals 2[b_k = 1]. So the signed sum over e_S equals 2^{|S|} times the sum, over the b with b_S = 1, of c_{delta,b} (-1)^{b_{S^c}.(e xor delta)_{S^c}}. As e_{S^c} varies, this is a Fourier transform in b_{S^c}. It vanishes for every e_{S^c} iff c_{delta,b} = 0 whenever b_S = 1, with S = D \ supp(delta). That is, X^delta Z^b is forbidden iff, at every k in D, delta_k = 1 or b_k = 1. ∎ *Exact check* (pauli_exact.py, rational arithmetic with python-flint): for all 7 nonempty D the two families of functionals have equal rank and equal joint rank. The ranks are 48 / 36 / 27 for |D| = 1 / 2 / 3, so the allowed spaces have dimensions 16 / 28 / 37. The stored H.7 solutions satisfy both forms to the same precision (pauli.py).
*Sanity check.* For a process function, U_o = X^{w(o)} and K = X^{w(o) xor w(o')} is a single Pauli. It is allowed iff w_k(o) = w_k(o') for some k in D, which is the exclusivity lemma of Section 1. So H.8.1 is the operator-valued version of exclusivity, with a span in place of a union.

**H.8.2 Ancillas add nothing in family C [proved].** Family C is pure under local unitaries with arbitrary finite ancillas iff it is pure without them, iff H.8.1 holds. This settles the question left open after H.7.1.
*Proof.* With ancillas, rows of M are labelled (o, t', y). The row inner product is sum_e K[e, e xor delta] prod_k N_k(e_k), with N_k(e) = sum_x U_k[(o_k,y_k),(e,x)] conj U_k[(o'_k,y'_k),(e xor delta_k, x)]. As in H.7.1, N_k spans C^2 unless (o_k,y_k) != (o'_k,y'_k) and delta_k = 0, in which case it spans (1,-1). The parties with (o_k,y_k) != (o'_k,y'_k) form a set D' that contains D. If o = o', then K = 1 and every condition holds trivially. If o != o', the condition for D' is a further signed sum of the condition for D, because S' = D' \ supp(delta) contains S. So it is implied. ∎ So the 13 H.7 solutions are pure with ancillas exactly, not just numerically.

**H.8.3 Causal structure, read off K [proved].** In family C:
- (no self-influence) K_{o, o xor e_j} in 1_j (x) U(4) for every o and j;
- O_j influences I_k (BLO sense) iff some K_{o, o xor e_j} acts non-trivially on k;
- party k is operator-first iff every K_{o,o'} acts trivially on k, i.e. U_o = (1_k (x) R_o) U_0;
- party j is operator-last iff K_{o, o xor e_j} is a scalar for every o.
*Proof.* The Heisenberg pull-back of an observable A on I is sum_o |o><o| (x) G_o(A), with G_o(A) = sum_x U_o^dag A^{(x)} U_o (x) X^x on T. Here A^{(x)} is the part of A whose matrix entries connect e to e xor x. The register T and the sink record o make the pull-back block diagonal in o. Independence of o_j for every A supported on I_k means that U_o^dag sigma_k U_o is the same for o and o xor e_j for every Pauli sigma_k. Equivalently, K commutes with every Pauli on k, so it is trivial on k. For lastness take A on all of I; then K commutes with everything, so it is a scalar. The first item is H.8.1 with |D| = 1. Operator-first follows by composing along edges of the cube {0,1}^3. ∎ So "no first and no last party" means: every party k has some cube edge whose transition acts on k, and no direction j has only scalar transitions.

**H.8.4 Monomial switchboards are PF blends for every source state [proved].** If every U_o U_0^dag is monomial (a permutation matrix times a diagonal phase), or more generally if the rank-one projectors P_{o,i} := U_o^dag |i><i| U_o all commute, then p_phi is in conv(PF) for every phi.
*Proof.* Commuting rank-one projectors that sum to 1 over i, for each o, are the projectors onto one common orthonormal basis {b_j}: P_{o,i} = |b_{j(o,i)}><b_{j(o,i)}|. For phi = b_j the induced p is 0/1. It is valid by Appendix A, since b_j is a legitimate source state (H.8.1 does not mention phi). A 0/1 valid classical process is a process function. Then p_phi = sum_j |<b_j|phi>|^2 p_{b_j}. ∎ This covers the Ring (all single-PF lifts and their pure phase variants) and the classical reversible case (D.6).

**H.8.5 Single-party edges preserve that party's marginal [proved].** If o and o' differ only at k, then psi_o = (1_k (x) R) psi_{o'}. So the distribution of e_k is the same under o and o'. Party k cannot signal to itself even in superposition. Two-party differences give K in A_A + A_B. This is a sum, and it contains unitaries such as cos(theta) X_A + i sin(theta) X_B, which no single process function produces. That interference is what a proof would have to control.

**The hull question [numerical; superseded by H.12: the answer is no].** By H.8.2, "do the H.7.1 conditions force p into conv(PF)?" is exactly the purification conjecture restricted to the Switchboard. Equivalently, F_m(U) := sum over (s,i,o) in m of s P_{o,i} <= 0 (operator inequality) for every facet m of the 37-dim hull, whenever U satisfies H.8.1. The search of Appendix I minimises the exact residual R(U) = sum over o != o' of the squared forbidden Pauli coefficients, at prescribed facet-82 violation v = lambda_max(F_m) > 0. It never found R -> 0. The minimum found was R >= 0.31 v^2 over 108 runs (random, Lugano and H.7-solution starts; v = 0.01 to 0.9). **No counterexample.** Note that the class is compact: if inf R = 0 at some fixed v > 0, a limit point would be an exact counterexample. So the observed quadratic floor is the quantitative form of the evidence. It is not a proof.

**Where a proof stopped.** H.8.4 covers the commuting case. The Shadows (lug_21-23) are non-commuting and genuinely non-separable, yet inside the hull. So a general proof must decompose p_phi into PFs without a common eigenbasis, for instance by a phi-dependent basis or by an SOS identity of the form -lambda_max(F_m) >= -c sqrt(R). The numerics suggest c ~ 1.8 for facet 82. I did not find such an identity. An exact SOS search in the 8 x 64 complex entries of U (quartic in U) was not set up.

### H.9 Toward a structure theorem: three binary parties, no operator-first and no last party (Oct 22 2026) [partial; proved vs conjectured marked]

**Proved.**
1. (H.6.2, H.1) A purifiable W outside conv(PF) has only purifications with no operator-first party and no W-level last party. An operator-last party makes W independent of that output, so H.1 applies. Purifications with an operator-last party are therefore also excluded.
2. (Family C, H.8) Inside the Switchboard the open class is the set of 8-tuples of unitaries with K_{o,o'} in A_{D(o,o')} (H.8.1), with every party acted on by some edge transition and no direction scalar (H.8.3). On this class purity with and without ancillas coincide (H.8.2). The commuting/monomial sub-class lies in conv(PF) for every source state (H.8.4). That sub-class contains the whole Ring (the 64 Lugano-orbit lifts).
3. (Family B) The Chorus shows that the open class contains purifications of causally separable W (H.7). So any structure theorem must be a statement about the record W, not about V: "no first mover in V" does not force non-separability.
4. (No reduction to a canonical form) D.4 already shows that no hidden classical label can be read off. H.8.1 shows the Switchboard transitions live in sums of algebras rather than unions, so purifications are not, up to local unitaries, coherent controls over single process functions. The Shadows are explicit numerical examples (non-monomial C_o).

**Conjectured (not proved).**
- (C1) [REFUTED, H.12.1] Switchboard conjecture: H.8.1 implies F_m(U) <= 0 for every hull facet m. Quantitatively, lambda_max(F_m(U)) <= c sqrt(R(U)) with c ~ 1.8 for facet 82 (Appendix I, numerical).
- (C2) Every three-party binary purification with no operator-first party can be brought, by local unitaries on source and sink and an enlargement of the source, into Switchboard form with the sink recording (o, i). D.1 gives the orthogonal record of (o, i), but not the controlled-unitary structure of the source. If (C1) and (C2) both held, the three-party binary conjecture would follow. Neither is proved, and (C2) is a guess based only on D.1.

**Not attempted.** Larger sources than C^8 (x) C^8 inside family C (the C_o would then be isometries from a larger S); non-binary alphabets.

### H.10 Attacking (C1) directly: flip-superposing boards (Oct 22 2026) [proved parts; hull statement numerical]

Goal: prove that the Pauli rule (H.8.1) forces p_phi into conv(PF) for every source state phi, or find an exact counterexample. **Neither was achieved.** Below: three proved negative or structural facts that close natural routes, and an exhaustive exact family of genuinely non-commuting boards that is numerically inside the hull for every facet. No counterexample was found. Code: code/stochastic/cyclic/switchboard/c1/.

**H.10.1 No p-preserving twirl reduces to the commuting case [proved].** A common left factor U_o -> L U_o preserves the Pauli rule. It preserves every p_phi iff L^dag |i><i| L = |i><i| for all i, i.e. iff L = D is diagonal (phases on input strings). Right factors U_o -> U_o W preserve the rule but move phi to W phi. But D leaves every projector P_{o,i} = U_o^dag |i><i| U_o unchanged. So any average over such maps leaves the P_{o,i}, and their commutation relations, exactly as they were. A reduction of the Shadows to H.8.4 by symmetrisation is therefore impossible. A proof must handle non-commuting P_{o,i} head-on.

**H.10.2 The degree-2 (Shor) relaxation is vacuous [proved].** Relax u = (vec U_0, ..., vec U_7) to a moment matrix X ⪰ 0 for E[u u^dag]. Then the Pauli rule (linear in the cross blocks E[U_o (x) conj U_o'], o != o'), unitarity (linear in the diagonal blocks) and p (diagonal blocks) are all linear in X. Take X block-diagonal, with blocks vec(U*_o) vec(U*_o)^dag for arbitrary unitaries U*_o. All cross blocks vanish, so the rule holds, and p(i|o) = |U*_o[i,0]|^2 is an arbitrary stochastic matrix (even an invalid one). So no degree-2 certificate in the board entries exists for any facet. This parallels C.5 and D.8: certificates must be at least quartic in U.

**H.10.3 Pairwise exclusivity characterises binary 3-party PFs [proved, exhaustive].** A backtracking enumeration of all 8^8 maps w: {0,1}^3 -> {0,1}^3 finds exactly 744 maps with "for all o != o', some k in D(o,o') has w_k(o) = w_k(o')". These are the 744 PFs. So for single-Pauli boards U_o = X^{w(o)} the Pauli rule is *equivalent* to w being a PF (twoterm.py).

**H.10.4 Two-term boards: an exact family of flip-superposing switchboards [proved: structure; numerical: hull].**
Let U_o = cos(t) X^{w1(o)} + i sin(t) X^{w2(o)} = X^{w1(o)} exp(i t X^{d(o)}), with d = w1 xor w2 and 0 < t < pi/2. Each U_o is unitary, because X-strings commute and square to 1. This is the simplest board that superposes two different flip patterns, the feature of the Shadows (H.8.5).
- *Rule, exactly.* For o != o', K = c^2 X^{a xor a'} + s^2 X^{b xor b'} + i c s (X^{b xor a'} - X^{a xor b'}). Distinct X-strings are linearly independent, and only the two cross terms can cancel (iff d(o) = d(o')). So the rule says: w1 and w2 are PFs (H.10.3), and for every o != o' either d(o) = d(o'), or both cross strings w2(o) xor w1(o') and w1(o) xor w2(o') are allowed (zero at some k in D). The condition does not depend on t.
- *Enumeration [exact].* There are 40,256 admissible ordered pairs: 744 with w1 = w2 and 39,512 with w1 != w2. 5,208 have d constant, so U_o = X^{w1(o)} W with a common W. That is a PF lift with source W phi, a blend by H.8.4 [proved]. The other 34,304 have non-constant d: 20,736 take 2 values, 13,056 take 3 and 512 take 4. In a random sample of 500 of these, all 500 have non-commuting P_{o,i}. So H.8.4 does not apply to them.
- *Hull test [numerical].* The family is invariant under the 384 symmetries, giving 237 orbit representatives. For each representative, each t in {pi/12, pi/8, pi/6, pi/4, pi/3, 3pi/8, 5pi/12} and **each of the 29,344 hull facets** (normaliz list, mapped to p-coordinates and verified on all 744 PFs), I computed lambda_min of the facet operator sum g[i,o] P_{o,i} + g0·1. Its non-negativity means that *every* source state phi gives statistics on the correct side. The minimum over all of these is -1.7e-14, i.e. zero to float64 precision. So every two-term board tested lies in conv(PF) for every source state, including the 34,304 non-commuting ones. This is numerical (a float64 eigenvalue test on a grid in t), not a proof. An exact version would need, per (representative, facet), a 16 x 16 Gram certificate for the univariate matrix form c^2 A + s^2 B + cs C. That is not done.
- *Counterexample status.* None. A counterexample would need a board family not of this form. The continuous search of H.8/Appendix I (all of U(8)^8) did not find one either.

**H.10.6 Coset-transport theorem; all two-term boards are PF blends [proved].** Let U_o = X^{a(o)} G_{kappa(o)}, where kappa partitions the outputs into classes and each G_kappa is a unitary in the span of {X^h : h in H_kappa} for a subgroup H_kappa. Suppose every *class-constant selection* o -> a(o) xor h_{kappa(o)}, with h_kappa in H_kappa, is a PF. Then p_phi is in conv(PF) for every source state phi, by the explicit decomposition below.
*Proof.* Let mu_j = |phi_j|^2 and r_kappa(j) = |(G_kappa phi)_j|^2. Then p(j xor a(o) | o) = r_{kappa(o)}(j). G_kappa is block-diagonal on the cosets j + H_kappa and unitary there, so r_kappa and mu have equal mass on every coset. Choose a transport plan pi_kappa(j, h) >= 0, h in H_kappa, with sum_h pi_kappa(j,h) = mu_j and sum over (j,h) with j xor h = j' of pi_kappa(j,h) = r_kappa(j'). Such a plan exists because the masses agree coset by coset. Put lambda(j, (h_kappa)) = mu_j prod_kappa pi_kappa(j, h_kappa)/mu_j, and let the PF of the term be o -> j xor a(o) xor h_{kappa(o)}. A translate of a PF by j is a PF. The weights sum to 1, and the marginal at (i, o) is sum_j pi_{kappa(o)}(j, i xor a(o) xor j) = r(i xor a(o)) = p(i|o). ∎
*Two-term boards.* Here a = w1, kappa = level sets of d = w1 xor w2, and H = {0, d}. coset_check.py checks every class-constant selection exactly, for all 39,512 non-trivial admissible pairs. **The hypothesis holds for every pair** (0 failures). So **every two-term board is a PF blend for every t and every phi** [proved: the theorem above plus an exhaustive exact combinatorial check]. This turns the H.10.4 numerics into a proof, for all pairs and not just the 237 representatives. The hypothesis is genuinely needed: for no pair are all 256 *unrestricted* selections PFs. coset_decomp.py builds the decomposition for 300 random (pair, phi, t) and reproduces p to 7e-16 (sanity check).
*Limits.* The theorem also covers any X-type board that satisfies the selection hypothesis. The counterexample of H.12 is an X-type board with 8-term boards for which the hypothesis fails.

**H.10.5 What a proof of (C1) must do** (written before H.12; (C1) is false). By H.10.1 and H.10.2, it must be non-symmetrising and at least quartic in U. The two-term family suggests the natural next target, which is open: for d(o) taking two values, U_o = X^{w1(o)} exp(i t X^{d(o)}). Here the boards split into two commuting classes, and p_phi should decompose as a blend over a measurement adapted to the two classes. I did not find that decomposition.

### H.11 Toward (C2): reducing a general purification to Switchboard form (Oct 22 2026) [partial]

**H.11.1 Input copying preserves purity [proved].** Given any purification (V, psi), add a source register T = I and define V' = (CNOT from I to T) V. This copies each input string into the sink, XORed with t. For the parties, this is a local unitary with an ancilla routed from source to sink: party k applies CNOT(I_k -> T_k) and then its own unitary. AFNB purity allows such ancillas. So V' is pure, induces the same W on psi (x) |0>, and its sink holds an exact copy of i.

**H.11.2 Generalized switchboards [proved].** Call V a generalized switchboard if V|o, s, t> = sum_e |e>_I |o>_{F1} (x) (C_o (s))_{e} (x) |e xor t>, where each C_o : S -> I (x) F' is unitary and F' is any extra sink. The proof of H.7.1/H.8.1-H.8.2 goes through block by block: V is pure (with or without ancillas) iff, for every o != o' and every pair of F' basis labels (f, f'), the 8 x 8 block K^{f f'} of C_o C_o'^dag satisfies the Pauli rule. The row inner products factor exactly as before, with the F' labels as spectators. H.8.3 also carries over, with "scalar" replaced by "acts only on F'". **So (C1) for generalized switchboards is the operator-valued Pauli rule.**

**H.11.3 The gap [open].** After H.11.1, a purification is a generalized switchboard iff some sink unitary makes the sink record o *for every source state s*, not only for psi. D.1 gives the orthogonal record of (o, i) on psi alone. Purity constrains V on all of P, but I found no argument that it forces an o-record off psi, and no counterexample. Every purification constructed so far has one (single-PF lifts, C.1 lifts, families A-C). So (C2) is reduced to: **does every pure V that purifies a classical W admit a sink unitary under which o is recorded on every source state?** Not proved.

**H.11.4 Per-machine recording is false [proved].** Take a coherent control: a source qubit r, passed on to the sink, with V = |0><0|_r (x) V0 + |1><1|_r (x) V1. Here V0 is a PF lift (it records o) and V1 is a pure comb A -> B -> C (I_B = O_A and I_C = O_B wired, I_A from the source, O_C to the sink), which does not record o_A or o_B. V is pure, since the induced map is |0><0| (x) M0 + |1><1| (x) M1. On the source |0>_r (x) psi it purifies the classical W of V0. On |1>_r (x) s, the values o_A and o_B end up in the parties' inputs, not the sink, so no sink unitary can record them. So "every purification records o on every source state" (H.11.3) is false. A reduction must first restrict the source to a suitable subspace containing psi. Whether such a sub-purification always exists is open. After H.12 this question no longer decides the conjecture, which is false. It remains a question about the shape of general purifications.

### H.12 A purifiable classical process outside the PF hull: the purification conjecture is false (Oct 22 2026) [proved: exact arithmetic + paper proofs; independently re-derived (H.12.2); Lean-checked with two gaps (H.12.3)]

**Theorem H.12.1.** There is a valid three-party binary classical process p with an AFNB purification (a pure process, i.e. unitary under all local unitaries with arbitrary finite ancillas) such that p is **not** a mixture of process functions. So the "only if" half of the conjecture of Section 9 is false, and so is (C1) of H.9. This is the main result of the note (Theorem 9.1).

**The machine.** It is a Switchboard (family C, H.7) with X-type boards. Let Hd be the 3-qubit Hadamard. Put U_o = Hd diag(i^{m_o(z)}) Hd, so U_o acts diagonally in the Hadamard basis |z^>. The exponents m_o(z) in {0,1,2,3}, for z = 000, ..., 111 in binary order, are:

| o | m_o(z) |
|---|---|
| 000 | 0 3 0 0 2 0 3 0 |
| 001 | 0 3 2 2 2 0 3 0 |
| 010 | 0 3 0 0 2 1 3 1 |
| 011 | 0 3 2 2 2 1 3 1 |
| 100 | 0 1 2 2 2 2 1 2 |
| 101 | 0 1 0 0 2 2 1 2 |
| 110 | 0 1 2 2 2 3 1 3 |
| 111 | 0 1 0 0 2 3 1 3 |

V|o, s, t> = sum_e U_o[e, s] |e>_I |o>_F |e xor t>_F. The source state is phi (x) |0>_T, with phi = (|011> + e^{-i pi/4} |100>)/sqrt 2, and p(i|o) = |<i|U_o phi>|^2.

**Verification** (code/stochastic/cyclic/switchboard/c1/exact_cex.py, log exact_cex.log; all in exact rational arithmetic in Q(zeta_8), no floating point):
1. Every U_o is unitary.
2. All 2,232 forbidden Pauli coefficients of all K_{o,o'} (o != o') are exactly 0, so the Pauli rule H.8.1 holds. By H.8.1 (equivalence with H.7.1), H.7.1 and H.8.2, V is pure with and without ancillas. These are paper proofs, not Lean.
3. p is real with entries in Q(sqrt 2) (cex_p_exact.json). Every column sums to 1, and all 64 deterministic local interventions give total probability exactly 1. So p is a valid classical process.
4. Facet 1741 of the normaliz list, mapped exactly to p-coordinates, gives an integer inequality g.p + g0 >= 0. It is checked exactly on all 744 PFs, is tight on 418 of them, and hence holds on conv(PF). On p it equals **1/4 - (3/16) sqrt 2 < 0**. So p is not in conv(PF).

**Independent checks [numerical, not needed for the proof]** (direct_purity.py, verify_cex.py, cex_structure.log):
- Direct simulation without using H.7.1/H.8: over 30 Haar samples with ancilla dimensions 1-3, max |M M^dag - 1| = 2.7e-15 and max |M^dag M - 1| = 2.6e-15. V itself is unitary.
- Simulating all 64 deterministic interventions through V (party unitaries |i,x> -> |f(i) xor x, i>) reproduces p(i|f(i)) to 1.3e-15.
- LP distance from p to conv(744 PFs) is 0.0607 (L1). Over source states the largest is 0.828 = 2(sqrt 2 - 1), at the top eigenvector of the facet operator.
- No party is operator-first (residuals 0.31 / 0.25 / 0.31), the causal graph is complete, and every U_o has full X-support (8 Pauli terms). This is consistent with H.6 and H.10.6: the coset hypothesis fails for it.

**How it was found.** The search of H.8/Appendix I over all of U(8)^8 never got below R ~ 0.31 v^2. Restricting to X-type boards (64 phases, xtype.py) gave exactly pure boards with facet violations straight away (xtype.jsonl, e.g. xt_0_20_0.npy: R = 1e-18, LP distance 0.44). Snapping the phases to multiples of pi/4 (snap.py) kept purity and violation, and the snapped phases turned out to be multiples of pi/2, giving the table above. **So the Appendix I quadratic floor was an artefact of local optimisation, and is withdrawn.**

**What survives.** The "if" half (C.1). The classical version D.6, which says *classical* reversible purifiability gives exactly the PF hull. Two parties (G). All the structural theorems (H.1, H.2, H.6, H.8, H.10.6). The exact non-purifiability certificates for E_ex1 and orbits 7 and 50 (C.2). The corrected statement: **quantum purifiability is strictly weaker than being a mixture of process functions, already for three binary parties, and the gap is witnessed by a Switchboard with no operator-first party.** Open: the exact purifiable set; whether it is a polytope; whether the vertex orbits 8, 10, 20 and the other sampled orbits are purifiable after all; and the reach of X-type boards.

**H.12.2 Independent re-derivation [exact, with float cross-checks].** A separate verification, code/stochastic/cyclic/switchboard/verify_h12/verify.py (log verify.log), was written from the text of this section alone and uses none of the code above.
- (0) Each 8U_o has Gaussian-integer entries, and (8U_o)(8U_o)^dag = 64·1 exactly.
- (2a) Purity is checked directly, not via H.7.1/H.8. The induced map is multi-affine in the three local operations, so purity reduces to an exact identity over 125 slot combinations. The result is PASS.
- (2b) 1,200 random trials, with isometries and ancilla dimensions 1 to 5, give max |M^dag M - 1| = 2.0e-15 [numerical]. A control with board 000 perturbed gives 3e-2, as it should.
- (3) p >= 0 and its columns sum to 1, exactly. All 64 deterministic interventions give total probability exactly 1, which covers all local stochastic interventions by multi-affinity.
- (4) The 744 PFs are re-enumerated by brute force over all 8^8 maps. The paper inequality has minimum 0 on them, is tight on 418, and takes the value 1/4 - (3/16) sqrt 2 on p. The referee's own rational separating inequality takes the value 1 - (3/4) sqrt 2 < 0 on p and is verified exactly on all PFs. The membership LP is infeasible.
- (5) A full circuit simulation reproduces p to 2.2e-16 [numerical].

**H.12.3 Lean formalisation [proved in Lean 4 + Mathlib; two gaps].** lean/PFUL/CounterexampleData.lean and lean/PFUL/Counterexample.lean (lean/STATUS.md, Round 6) prove

    theorem purification_conjecture_false :
      ∃ p, Valid p ∧ Purifiable p ∧ p ∉ convexHull ℝ PFset

The only axioms are propext, Classical.choice and Quot.sound. There is no `sorry` and no `native_decide`; finite computations use `decide +kernel`. The definitions, all in that file, are as follows.
- `IsPure V`: for every family of finite ancilla types a_k and every local unitary A_k on Bool × a_k, the link product `compose V A` is unitary.
- `Purifiable p`: some pure V on a 64-dimensional source and sink, with a normalised source state, induces p via p(i|o) = Σ_f |<i,f|V|o,ψ>|^2.
- `Valid p`: p >= 0, and total probability is 1 under every product of local stochastic maps.
- `PFset`: the 0/1 points of maps w with a unique fixed point for every local deterministic intervention.

The key lemmas are as follows.
- `board_mem_unitaryGroup`: each U_o = Hd·diag(i^m)·Hd is unitary.
- `isPure_Vsb`: the Switchboard is pure. The proof is a direct multilinear reduction, independent of the paper's H.7.1/H.8.2.
- `valid_pcl`.
- `Lg_nonneg_of_isPF` and `Lg_pcl_neg`: L(p) = (32 - 24 sqrt 2)/128 < 0.
- `pcl_not_mem_convexHull`.
- `purifiable_pcl`.

**Gaps.** (i) Closed for countable ancillas, as an isometry (Round 9, `PFUL/CounterexampleInf.lean`). Each ancilla is now any countable type κ_k with a unitary A_k on ℓ²(κ_k) (finite ancillas are the special case where κ_k is a Fintype). The composed kernel `composeOp V A`, built from the entries ⟨e_r, A e_c⟩, is the matrix `compose` with absolutely convergent ancilla series. `isPureKer_Vsb` shows that for the Switchboard these columns are orthonormal in ℓ²(P × Πκ_k). `isPureInf_Vsb` then gives a linear isometry U of ℓ² with ⟨e_r, U e_c⟩ = `composeOp Vsb A`. `IsPureKer.isPure` checks that the new notion agrees with the matrix `IsPure` on finite ancillas. `purification_conjecture_false_inf` restates the counterexample with `PurifiableInf` (infinite-ancilla purity together with finite purity). Remaining gap: we prove isometry, not unitarity, for infinite ancillas. Surjectivity would need the rows to be orthonormal too, and the scalar-key argument does not give that. (ii) Partly closed (Round 8). `isPF_iff` and `valid_pfPoint` (Round 7) link the process-function hull to `PFUL.Countable.IsProcessFunction` and the general column identity. `compose_eq_link` and `compose_congr_choiVec` show that `IsPure` is a property of the Choi vector |V⟩⟩, and `Vsb_pure_choi` packages `isPure_Vsb` with W = |Vsb⟩⟩⟨⟨Vsb| (Hermitian, W² = (Tr W)W), the form used in `PFUL.Choi`. That `Valid` equals `PFUL.Validity.ValidWith` for this 3-bit process is still checked on paper only.

**Caveat (revised).** The purity step now has three supports. The first is the paper proofs of H.7.1 and H.8.1-H.8.2, with the exact Pauli check. The second is the referee's direct exact criterion (H.12.2). The third is the Lean proof `isPure_Vsb` (H.12.3). None of the three has been peer reviewed. The earlier recommendation to formalise before announcing has been met, subject to the two gaps above.

**Quadratic robustness near facet 82 (Appendix I) [false: H.12 has R = 0 and a facet violation].** A proof of v <= c sqrt(R) would imply (C1) for facet 82 at R = 0. None of the routes above gives it. H.10.2 shows that any SOS proof must be at least quartic in U.

### H.13 Toward the purifiable set: exhaustive Z_4 X-type boards, a rational counterexample, convexity (Oct 22 2026) [proved: H.13.1, H.13.2 (exact rational arithmetic); numerical: H.13.3-H.13.4]

Code: code/stochastic/cyclic/switchboard/h13/ (xenum.py, canon.py, analyze.py, simple_phi.py, exact_rational.py; logs *.log). Write Purif for the set of purifiable three-party binary classical processes (any finite source and sink), Valid for the valid polytope.

**H.13.1 Purif is convex, and conv(PF) ⊊ Purif ⊊ Valid [proved].** Let V_1, V_2 purify p_1, p_2. Add a control qubit c to the source, prepared as sqrt(λ)|0> + sqrt(1-λ)|1>, and route it straight to the sink. Set V = |0><0|_c ⊗ V_1 + |1><1|_c ⊗ V_2, padding the smaller one with an idle register. Composing V with any local operations A gives |0><0| ⊗ (V_1∘A) + |1><1| ⊗ (V_2∘A). That is block diagonal with unitary blocks, so V is pure. The parties never touch c, and tracing the sink gives λp_1 + (1-λ)p_2. So Purif is convex. It contains conv(PF) (C.1) and is strictly larger (H.12, H.13.2). It is strictly smaller than Valid: the exact certificates of C.2 (E_ex1, orbits 7 and 50) are valid but not purifiable. ∎ The same argument shows that, for one fixed board family, the set of p it induces over all source states (mixed sources allowed) is a linear image of the 8x8 density matrices. Purif contains the convex hull of these spectrahedral shadows. Whether Purif is a polytope is open.

**H.13.2 A rational, real counterexample with half the Pauli support [proved; exact rational arithmetic, no irrationals].** Take U_o = Hd·diag((-1)^{n_o(z)})·Hd with n_o(z) ∈ {0,1}. Rows o = 000..111, columns z = 000..111:

| o | n_o(z) |
|---|---|
| 000 | 0 0 0 0 0 0 0 0 |
| 001 | 0 0 1 1 1 1 1 1 |
| 010 | 0 0 0 0 1 0 1 0 |
| 011 | 0 0 1 1 0 1 0 1 |
| 100 | 0 0 0 1 0 0 0 1 |
| 101 | 0 0 1 0 1 1 1 0 |
| 110 | 0 0 0 1 1 0 1 1 |
| 111 | 0 0 1 0 0 1 0 0 |

Each U_o is a real orthogonal matrix with entries in (1/4)Z. Each U_o U_000^T has 4 X-Pauli terms; the H.12 board has 8. Take the source phi = (|000> + |001> + |010> - |101>)/2. Then p(i|o) = (U_o phi)_i^2 has entries in {0, 1/16, 1/4, 9/16} (table in exact_rational.log). exact_rational.py checks the following in Fraction arithmetic only.
- (1) Every U_o is orthogonal.
- (2) All 2,232 forbidden Pauli coefficients vanish, so the board is pure with and without ancillas (H.8.1-H.8.2).
- (3) p is valid: all 64 deterministic interventions give total probability 1.
- (4) Facet 16962 (orbit 91; tight on 436 PFs, range 2 on PFs) takes the value **-1/8** on p.

The source (|000> + |001> + |010>)/sqrt 3 also gives a rational p, and that p violates facets 16962 and 15629 by -1/12. **So irrational phases, Z_4 phases and full Pauli support are all inessential: ±1 phases and 4-term transitions suffice.** By H.10.6, two-term boards cannot do this, so 4 terms is within one of the minimum. Whether 3-term X-type boards can violate a facet is open; none of the Z_4 boards below does.

**H.13.3 Exhaustive Z_4 X-type enumeration [exact enumeration; violations numerical].** Fix the gauge m_000 = 0 (a common right factor is absorbed into phi) and m_o(000) = 0 (global phases). The Pauli rule for X-type boards says: the Walsh-Fourier transform of i^{m_o - m_o'} vanishes on every a ⊇ D(o,o'). These are integer tests. Backtracking over the cube (xenum.py, exact) gives **exactly 13,105 pure Z_4 X-type boards**. Modulo output flips, party permutations and complex conjugation, they fall into 386 classes (canon.py). For each class, analyze.py computes max over phi of the violation of all 29,344 facets, as -λ_min(Σ g·P_{o,i} + g_0) divided by the facet's range on PFs [numerical, float64].
- 12 of the 386 classes (216 boards) leave conv(PF). 2 of the 27 classes with real (±1) phases do; H.13.2 is one of them.
- No board whose transitions have at most 2 X-terms violates any facet, which is consistent with H.10.6. The violating classes have at most 4, 5 or 6 terms per transition (gauge m_000 = 0).
- The largest relative violation is **0.1404**, on orbit 91, reached by the ±1 class of H.13.2 at its optimal (irrational) phi. Facet orbit 82 (the H.12 facet) reaches 0.1036.

**H.13.4 Which facets purifiable processes violate [numerical, within Z_4 X-type boards].** 62 of the 93 facet orbits are violated by some board. The following 31 orbits are never violated in this family: 4-11, 14, 16, 19, 21, 24-31, 52-54, 57, 66, 67, 69, 75, 79, 81, 92. They are candidates for facets that remain valid on Purif. (Orbit 92 is the positivity orbit p(i|o) ≥ 0 and holds trivially; see H.17.5.) Maximum relative violation per violated orbit:
- 0.14: orbit 91.
- 0.10: orbits 82-84.
- 0.09: orbits 40, 45-47, 60, 61, 76, 78.
- 0.05-0.06: orbits 36-39, 41-44, 50, 51, 58, 59, 62, 63, 72, 73, 86-89.
- 0.02-0.04: the rest.
This is a lower bound on the violation over Purif, not the maximum. General boards, larger phase groups and non-X-type boards were not enumerated.

**Partial characterization (status).** Proved: Purif is convex, with conv(PF) ⊊ Purif ⊊ Valid. Two-term boards stay inside conv(PF) (H.10.6). The commuting/monomial boards do too (H.8.4). Four-term ±1 boards can leave it (H.13.2). Not proved: three-term boards; whether the 31 unviolated orbits are valid on all of Purif; whether Purif is a polytope; whether X-type boards already give all of Purif.

**H.13.5 Relation to Kunjwal-Oreshkov antinomicity [proved: exact rational decomposition; literature CITED, verified from arXiv:2307.02565v3 on Oct 23 2026].** Kunjwal and Oreshkov (ref. 36) call correlations *nomic* if they arise from classical processes in conv(PF), with arbitrary classical local operations, and *antinomic* otherwise. Two passages bear on this note.
- They observe that classical processes outside conv(PF) "fail to be reversibly extendible" (citing Baumeler's PhD thesis, ref. 30; compare D.6).
- They ask, as an open question: "can correlations realizable via unitarily-extendible process matrices display antinomicity?"

The boards of H.12 and H.13.2 are *quantum* unitary extensions of classical processes outside conv(PF). By the remark above, those processes have no classical reversible extension, so here quantum reversibility reaches classical processes that classical reversibility cannot.

**This does not resolve their question.** Being outside conv(PF) is a statement about the process p(i|o) on its fixed binary alphabets. Nomic correlations allow local operations that use a party's own setting and hidden alphabets of up to four values. We checked the correlation P(x|a) := p(i=x|o=a) of H.13.2, obtained with identity classical instruments, in the (3,2,2) scenario.
- We enumerated the nomic vertices with K-O Theorem 4: 152,128 deterministic correlations whose faithful process function has |I_k| ≤ 4. As a sanity check, the maximum GYNIN score over them is 5/8, which matches K-O Eq. (102).
- The H.13.2 correlation **lies in the nomic polytope**. An LP finds a decomposition with 23 vertices. Re-solved in Fraction arithmetic, it has rational weights in {1/144, 1/48, 1/24, 1/18, 1/16} and reproduces P exactly.

Code: code/stochastic/cyclic/nomic/ (nomic_check.py, nomic_check.log). So the H.13.2 correlation is nomic (though, by H.15.7b, not causal). The H.12 correlation and other quantum instruments on these boards have not been tested. Whether any instruments on a purifiable board give antinomic correlations remains open.

### H.14 Three-term boards, wider phase groups, exact per-orbit maxima (Oct 22 2026) [proved: H.14.1, H.14.2; exact algebraic values: H.14.3; numerical: H.14.4]

Code: code/stochastic/cyclic/switchboard/h13/ (z8enum.py, canonN.py, analyzeN.py, cert_z8.py, exactmax.py, threeterm.py; logs alongside).

**H.14.1 X-type boards with at most three terms are PF blends [proved].** Call a board X-type k-term if there is a common unitary W such that every U_o W is a combination of at most k X-strings. (W only moves the source: phi -> W^dag phi.)

*(a) No X-type unitary has exactly three terms.* Suppose U = X^a(α + βX^u + γX^v), with u, v, u xor v distinct and nonzero. Its eigenvalues are α + βχ(u) + γχ(v), over the four sign pairs (χ(u), χ(v)) ∈ {±1}^2. Unitarity needs all four to have modulus 1. Comparing them pairwise gives Re(αβ̄) = Re(αγ̄) = Re(βγ̄) = 0. Read α, β, γ as vectors in R^2: they would then be pairwise perpendicular, which is impossible when all three are nonzero. ∎

So an X-type ≤3-term board has U_o = X^{a(o)} G_o, with G_o = α_o 1 + β_o X^{d(o)} (unitary iff Re(α_o β̄_o) = 0 and |α_o|^2 + |β_o|^2 = 1).

*(b) Theorem.* Every such board gives p_phi ∈ conv(PF) for every phi. This generalises H.10.6: t, the phases and d may all vary with o.

*Proof.* Put o and o' in the same class when G_{o'} ∝ G_o. If G_{o'} ∝ G_o X^{d}, rewrite a(o') -> a(o') xor d, which puts o' in the same class. Then:
- Same class: K = X^{a xor a'}, and the rule makes a xor a' allowed.
- Different classes with the same d: G G'^dag has both 1 and X^d with nonzero coefficients, so a xor a' and a xor a' xor d are both allowed.
- Different d, both two-term: the four strings a xor a', a xor a' xor d, a xor a' xor d', a xor a' xor d xor d' are distinct with nonzero coefficients. So all four are allowed. One-term classes are the special case β = 0.

Hence every class-constant selection o -> a(o) xor h_{κ(o)}, with h_κ ∈ {0, d_κ}, is pairwise exclusive on every pair (o, o'). By H.10.3 (exhaustive and exact: pairwise exclusivity ⇔ PF), it is a PF. The coset-transport construction of H.10.6, with H_κ = {0, d_κ}, then writes p_phi as a PF blend. ∎

This replaces the enumeration in H.10.6 with a proof that uses no computer apart from H.10.3. With H.13.2, the threshold for X-type boards is now exact: **≤3 terms always blend, and 4 terms can violate the hull.**

*(c) General (non-X) three-term unitaries [proved form; hull question open].* Write U = αP + βQ + γR with Paulis P, Q, R, so P^dag U = α + βA + γB.
- If A and B commute, the argument of (a) applies, so U has at most 2 terms.
- If A and B anticommute, unitarity forces U ∝ P exp(i t(cos f A' + sin f B')) with Hermitian A' ∝ A and B' ∝ B.

A left Z-string factor leaves p unchanged but does change the Pauli rule. So Paulis with Z components genuinely enlarge the family. threeterm.py anneals over the discrete structure (P_o, A_o, B_o) to satisfy the rule identically. In 30 runs over 7 seeds it never reached an admissible board with genuinely anticommuting terms: the residual stayed at 15-22 [numerical, inconclusive]. **Whether non-X three-term boards can leave the hull is open.**

**H.14.2 Z_8 boards violate 8 of the 31 orbits that Z_4 never violated (full tables in Appendix J) [proved; exact arithmetic in Q(ζ_8)].** z8enum.py enumerates pure Z_8 X-type boards with the same gauge as H.13.3 and an exact integer Pauli test (in the basis 1, ζ, ζ^2, ζ^3 of Z[ζ_8]).
- There are exactly **500,081** boards, in 10,603 classes. As a cross-check, the same code with N = 4 gives the H.13.3 count 13,105.
- Float screen: 88 classes violate. Of these, 76 use odd powers of ζ_8. They reach 70 of the 93 orbits.
- cert_z8.py certifies the following exactly for class 10515, phases ζ_8^m with m given in cert_z8.log:
  - unitarity;
  - the Pauli rule, so the board is pure;
  - validity, for a Gaussian-rational source vector v;
  - a negative facet value of the form a + b sqrt 2, for **orbits 16, 19, 21, 24, 27, 29, 52 and 67**.
- The relative violations are 0.0021, 0.0019, 0.0021, 0.0014, 0.00026, 0.00025, 0.00057 and 0.00057.
- Remaining **never-violated orbits (23):** 4-11, 14, 25, 26, 28, 30, 31, 53, 54, 57, 66, 69, 75, 79, 81, 92. Orbit 92 is positivity (H.17.5), so 22 are genuine.
- Z_8 also raises the maxima on orbits 34, 35, 37, 38, 42, 44, 49 and 71, by 2-7% [numerical]. The overall maximum, 0.1404 on orbit 91, does not move.

**H.14.3 Exact per-orbit maxima over Z_4 X-type boards [exact algebraic numbers for float-selected maximisers].** For each violated orbit, take the (class, facet) with the largest float violation. Its maximum over source states is -λ_min(F), and λ_min is an exact root of the integer characteristic-polynomial factor in exactmax_part{1,2}.log (flint/sympy, from an exact rational facet g). Examples:
- Orbit 91: λ = (3 - sqrt 17)/4 on range 2, so relative violation **(sqrt 17 - 3)/8 ≈ 0.14039**.
- Orbits 82-84: root of 4x^2 - 4x - 1, so **(sqrt 2 - 1)/4 ≈ 0.10355**.
- Orbits 60, 61, 76, 78: root of 2x^2 - 3x - 1, on range 3, so **(sqrt 17 - 3)/12 ≈ 0.09359**.
- Orbits 32-35, 48, 49, 70: root of 4x^2 - 8x - 1, on range 4, so **(sqrt 5 - 2)/8 ≈ 0.02951**.
- The other orbits have roots of quartics up to octics.

These are exact values of the maximiser that the float screen picked. They are exact family maxima only up to that float argmax over (class, facet), and they are maxima for Z_4 boards, not for Purif (Z_8 already exceeds them on 8 orbits).

**H.14.4 Is Purif a polytope? Do X-type boards generate it? [evidence only].**
- For every orbit checked, the maximiser's optimum is irrational: a root of an irreducible polynomial of degree ≥ 2 (H.14.3). So each board's region is a curved spectrahedral shadow.
- The certified violations grow from Z_2 to Z_4 to Z_8: 2, then 12, then 88 violating classes; 62, then 70 orbits. Nothing has saturated.

This suggests, but does not show, that Purif (convex by H.13.1) is not a polytope, and that finite phase groups only approximate it. No proof either way. Whether non-X-type or ancilla boards add anything beyond X-type is open.

### H.15 What the results mean in spacetime (Oct 23 2026) [labels: PROVED = this paper; CITED = verified from the arXiv primary source on Oct 23 2026; INTERPRETIVE = our reading, not a theorem]

**H.15.1 The cited embedding framework [CITED].**
- Baumeler, Costa, Ralph, Wolf and Zych (arXiv:1703.00779, CQG 36, 224002 (2019); ref. 16) model classical deterministic dynamics as follows:
  - There are N compact, CTC-free "local regions" with spacelike past and future boundaries. They sit in an arbitrary Lorentzian manifold and may be traversed by CTCs.
  - An agent in region R applies any function f_R from the past-boundary state to the future-boundary state.
  - The exterior dynamics is a function w: O -> I from future boundaries to past boundaries. Consistency with free local choice is exactly "w∘f has a fixed point for every f", and the fixed point is then unique (their Thm 1). These w are the process functions (PFs) of this paper.
  - Their Thm 2: every PF extends to an invertible one by adding a source region (output only, "in the past" of all regions) and a sink region (input only, "in the future"). They describe realisations by reversible interactions inside the CTC region (Fig. 3), for example billiard-ball logic.
  - Their Thm 3: three regions form a PF iff fixing any one output leaves at most one-way signalling between the other two. Three parties can each be both in the past and in the future of the others.
- Tobar and Costa (arXiv:2001.02511, CQG 37, 205011 (2020); ref. 28) extend this to N regions, with inequivalent four-party PFs. They sketch a wormhole spacetime with pairwise-identified mouths and a billiard-ball computer that implements any PF (their Fig. 3).
- Baumeler and Wolf (arXiv:1507.01714, NJP 18, 013036 (2016); ref. 15) show that the logically consistent classical processes form a polytope. For three binary parties it is 37-dimensional, with 64 facets and 710,760 vertices, of which only 744 are deterministic (the PFs); the rest are non-deterministic. conv(PF) is their separate, strictly smaller "deterministic-extrema polytope" (744/8 = 93 classes). Processes outside it are, in their words, fine-tuned: every decomposition into deterministic processes uses logically inconsistent ones. [CITED; corrected Oct 23 2026: the earlier wording "the deterministic ones are its extremal points" wrongly suggested that all vertices are PFs.] Ref. 16 adds that non-deterministic classical processes need not have a classical reversible extension (its ref. [33]).
- Oreshkov, Costa and Brukner (arXiv:1105.4464, ref. 14) define process matrices from local quantum mechanics alone. They note that any process can be read as a CPTP map from the parties' outputs back to their inputs, "having the form of a CTC". They also show that bipartite classical processes are causally separable.
- Araújo, Feix, Navascués and Brukner (arXiv:1611.08535, Quantum 1, 10 (2017); ref. 17) add a global past P and future F:
  - A process is pure iff it maps local unitaries to a unitary P -> F (their Thm 2: W = |U_w>><<U_w|).
  - The purification postulate: a process is physical only if it is part of a pure process. The motivation is reversibility of fundamental dynamics.
  - They exhibit a purifiable tripartite classical process that violates causal inequalities (their Sec. 7, the Lugano-type function).
- Lloyd et al. (arXiv:1005.2219, ref. 13) and Deutsch (ref. 10; Phys. Rev. D 44, 3197, journal version, not fetched here) give the P-CTC and D-CTC models. Ref. 16 (Sec. VII) states two comparisons. P-CTCs agree with the unitary-process predictions for valid unitary processes, but allow general unitaries at the price of nonlinearity and restricted local operations. D-CTCs allow arbitrary local operations but predict nonlinear evolution.
- Vilasini and Renner (arXiv:2203.11245, PRA 110, 022227 (2024); erratum PRA 114, 029903 (2026); companion letter PRL 133, 080201 (2024)) treat fixed acyclic spacetimes, Minkowski included. Theorem numbers [CITED]: Thm 3 (not fixed-order iff the signalling structure certifies cyclicity), Thm 4 (no-go: not fixed-order + relativistic causality + acyclic region structure is impossible), Cor 1 (no localisation of all in/outputs), Cor 2 (no time localisation in one global frame), Thm 5 / Cor 3 (a fine-grained fixed-order, hence causally separable, explanation with M = sum_k |R^{A_k^I}| >= N agents). Their systems are finite-dimensional and finite in number. Note that this no-go is due to Vilasini and **Renner**; the Colbeck papers are cited next. Relativistic causality is a compatibility condition between an information-theoretic structure and an acyclic spacetime. Realisations of indefinite-causal-order processes in such a spacetime (a) necessarily non-localise systems, and (b) admit a definite, acyclic causal-order explanation at a fine-grained level.
- Vilasini and Colbeck (arXiv:2109.12128, PRA 106, 032204 (2022); arXiv:2206.12887, PRL 129, 110401 (2022)) show that forbidding superluminal signalling alone does not rule out causal loops embedded in Minkowski space. They left open whether such loops are possible in 3+1 dimensions. **Update [CITED]:** Grothus and Vilasini (arXiv:2606.20476, 2026) prove that in every "conical" spacetime, including (d+1)-Minkowski for d > 1, all compatible embeddings of affects causal loops are degenerate (their Thm 1), in classical, quantum and post-quantum theories. Background: Grothus-Vilasini, CQG 43, 105008 (2026), arXiv:2403.00916.
- Further follow-ups [CITED, abstracts checked]: Salzger and Vilasini (arXiv:2404.05319, NJP 27, 023002 (2025)) map every QC-QC to a causal box on Fock space that is a fine-graining with acyclic order. Salzger and Selby (arXiv:2411.08266, Quantum 10, 1959 (2026)) define embeddability of a process via one of its decompositions. Ormrod, Vanrietvelde and Barrett (arXiv:2204.10273, Quantum 7, 1028 (2023)) show photonic quantum switches have cyclic coarse-grained but acyclic fine-grained causal structure, without assuming spacetime localisation. Vanrietvelde, Ormrod, Kristjánsson and Barrett (arXiv:2206.10042, Quantum 9, 1923 (2025)) build consistent processes from routed circuits, including Lugano, and conjecture that every unitarily extendible process arises this way. Tselentis and Baumeler (PRX Quantum 4, 040307 (2023)) give the siblings-on-cycles criterion for admissible causal structures.
- Paunković and Vojinović (arXiv:1905.09682, Quantum 4, 275 (2020)) show that every circuit can be immersed in a classical spacetime. Quantum-switch experiments in fixed spacetimes do not feature superposed causal orders; only a gravitational switch would.

**H.15.2 Dictionary: our objects as spacetime objects [INTERPRETIVE, built on ref. 16's set-up].**

    time ^                 sink region F (records o and the input string i)
         |                    ^
         |   +----------------+-----------------+
         |   |   CTC / wormhole region:         |   board U_o = coherent, reversible
         |   |   reversible scattering of the   |   interaction controlled by the
         |   |   three outgoing carriers o_A,   |   three outputs o (H.7/H.8 form)
         |   |   o_B, o_C with the source       |
         |   +--^------^------^-----------+-----+
         |      |      |      |  (mouths re-emit into the past of A, B, C)
         |    [A]    [B]    [C]   <- three CTC-free local regions; agents apply
         |      ^      ^      ^      any local operation (classical bit in/out)
         |   +--+------+------+--+
         |   |  source region S  |  prepares phi (the H.12 / H.13.2 state)
         |   +-------------------+

- *Parties.* A, B and C are ref. 16's local regions with binary inputs and outputs. Their classical inputs i_k and outputs o_k are the states on their past and future boundaries.
- *Source.* S is ref. 16's output-only region. Here it prepares a quantum state phi of the loop medium instead of a classical string. (In H.13.2, phi = (|000>+|001>+|010>-|101>)/2.)
- *Boards.* The family {U_o} is the unitary dynamics of the CTC region, conditioned on what the three agents emitted. Physically it is a scattering process in which the carriers sent by A, B and C (the controls o) act coherently on the loop medium before it is re-emitted, through the mouths, into the past boundaries as the inputs i.
- *Sink.* F receives what leaves the loop (the record of o and the scattered medium). Purity (H.8.2) says that S -> F is unitary for every choice of local unitaries, with or without the agents' private ancillas.
- *Classical process p(i|o).* It is what the three agents see when each measures their input in the computational basis, as in ref. 31's fixed-basis setting.

**H.15.3 What each result says in spacetime terms.**
1. *Purifiability = reversible, information-preserving loop dynamics [CITED definition + INTERPRETIVE reading].* Following ref. 17, a purification is a closed quantum system: everything that enters through S and through the agents' futures leaves through F and the agents' pasts, unitarily. Nothing is erased in the CTC region, so all irreversibility sits inside the agents' labs. Classically, ref. 16 Thm 2 shows that every PF is reversible in this sense, and D.6 shows that classical reversibility gives exactly conv(PF).
2. *The counterexamples (H.12, H.13.2) [PROVED] give a quantum time-travel signature [INTERPRETIVE].* p lies outside conv(PF). So no mixture of deterministic, self-consistent, classical CTC histories of the ref. 16 / ref. 28 kind reproduces these statistics. That includes every billiard-ball model with hidden random initial conditions. Reversible quantum loop dynamics does reproduce them.

   A facet inequality g·p + g0 >= 0 is then an operational witness. The three agents feed in deterministic local strategies, histogram their inputs, and evaluate the facet. A negative value, for example -1/8 for H.13.2, certifies that the loop is not a classical mixture of consistent histories. The rational counterexample needs only real ±1 phases, so the witness does not depend on complex amplitudes. The signature is quantum superposition of flip patterns, not complex phases.

   This is a stronger statement than "non-causal": the Lugano PF is already non-causal and fully classical (refs. 15-17). The H.12 statistics are non-causal *and* non-classical-deterministic. Caveat: the witness assumes that the agents' operations are the classical local operations of the model (ref. 16 Sec. III) and that the statistics are gathered over many runs.
3. *No first party (H.6.2) [PROVED].* Any purification of a process outside the hull has no operator-first party. In spacetime terms [INTERPRETIVE], no agent's input carrier can bypass the scattering. **Corrected Oct 23 2026:** this is an operator-level statement only. At the level of statistics, the H.13.2 process with phi = (|0>+|1>+|2>-|5>)/2 has B *marginally first*: B's input does not depend on any output [EXACT-CERTIFIED, H.15.6]. So relativistic causality, which constrains signalling only, allows B's region to sit in the causal past of A and C. What is excluded is that B's input is uncorrelated with the loop: by Theorem H.2 the A-C loop conditioned on (i_B, o_B) cannot be valid, and the check finds 32 invalid conditionals.
4. *Pauli rule (H.8.1) [PROVED] as a locality/consistency law of the loop [INTERPRETIVE].* When the outputs of the agents in a set D change, the change in the loop dynamics, K = U_o U_o'^dag, must lie in the span of operators that leave at least one changed party untouched. It is the operator-valued form of the PF exclusivity lemma; for single Paulis it reduces to that lemma exactly (H.10.3). Read in spacetime: no change of emissions may coherently act on all of the changed agents' returning carriers at once. That is the quantum generalisation of "one switch decides the direction of signalling" (ref. 16 Thm 3). It is the quantum analogue of the Novikov self-consistency principle quoted in refs. 14 and 16, as a linear constraint on the dynamics rather than on histories.
5. *Threshold (H.10.6, H.14.1) [PROVED] as minimum complexity of the loop [INTERPRETIVE].* Consider loop dynamics that act on the returning carriers only by superposing at most three bit-flip patterns at a time (X-type, ≤3 terms). They are always simulable by randomly chosen classical consistent histories: a transport plan gives the mixture explicitly. A quantum signature needs at least four coherently superposed flip patterns per transition (H.13.2 attains four). Status of non-X three-term dynamics with Z components (H.17, updated Oct 23 2026):
   - generic boards are PF blends (H.17.9) [PROVED];
   - tuned two-class boards (H.17.13) and boards containing the identity class (H.17.14) are PF blends [PROVED];
   - three non-identity classes: 18 of 61 G48 orbits are proved (H.17.15), and the rest is the subject of a running search;
   - four or more classes are OPEN.
   Every board proved to be a PF blend has a classical realisation as a mixture of the ref. 16 / ref. 28 reversible CTC histories, so it carries no quantum time-travel signature.
6. *Convexity (H.13.1) [PROVED].* A classical coin in S, routed untouched to F, selects which loop runs. So the set of loop statistics is closed under mixing, as for classical CTC models.
7. *Never-crossed facets (H.13.4, H.14.2) [numerical] and the polytope question (H.14.4) [evidence] [INTERPRETIVE].* 22 genuine facet orbits remain uncrossed by every board tested; a 23rd, orbit 92, is just positivity p(i|o) ≥ 0 and holds for every process (H.17.5). The 22 are candidate "classical-like" constraints that may bind every reversible quantum loop. Z_8 crossed 8 facet orbits that Z_4 did not, so the list is provisional. Ref. 15 shows that the classical consistent loops form a polytope. Our evidence suggests that reversible quantum loops form a curved convex set: the best violations are irrational and keep growing as the phase group grows. If that is right, the boundary between classical and quantum time travel is not a finite list of inequalities. That is not proved.

**H.15.4 Minkowski space instead of CTCs [CITED + INTERPRETIVE].**
- Every PF and every Switchboard here is a fixed linear map, so it can be simulated in ordinary spacetime with postselection (the P-CTC route, ref. 13), at the price of a success probability below 1.
- Without postselection, the Vilasini-Renner no-go (arXiv:2203.11245) applies to any Minkowski realisation of a process that is not causally ordered, which includes ours, since p is not causally separable. [PROVED: a classically causally separable process is a PF blend by Theorem H.2, and p is not; the exact check in H.15.6 also finds that p is not a fixed-order process, which is VR's actual hypothesis.] It would require time-delocalised (non-localised) systems, and would admit a fine-grained explanation with definite, acyclic causal order.
- So in Minkowski space our counterexample would not certify a causal loop. It would certify that the coarse-grained "events" A, B, C are not localised, and that the coarse statistics are not a mixture of consistent deterministic histories (H.12). **Downgraded Oct 23 2026:** the earlier claim that the fine-grained explanation "must itself be quantum and coherent" was not proved. The Lugano PF already needs non-localisation by VR Thm 4, since it is not fixed-order, so non-localisation alone does not separate our boards from classical PFs. Whether a classical fine-grained fixed-order model with more agents (VR Thm 5) can reproduce p is OPEN. Whether the fine-grained acyclic model can be chosen to respect the Pauli rule in a natural way we have not analysed.
- Vilasini-Colbeck (arXiv:2206.12887) left open loops in 3+1-dimensional Minkowski space without superluminal signalling. Grothus-Vilasini (arXiv:2606.20476) have since closed it in the negative for conical spacetimes [CITED]. Our results do not bear on that question: they concern CTC-type or non-localised realisations, not loops between localised events.
- On a genuine CTC spacetime (refs. 16, 28) the interpretation of H.15.3 applies directly, *if* one adopts the linear, unitary process model. That model is the one ref. 16 calls the natural quantum extension. It agrees with P-CTCs on valid unitary processes and differs from Deutsch's nonlinear model (ref. 16 Sec. VII).

**H.15.5 What is speculative.**
- No concrete metric, field theory or material realisation of the H.12/H.13.2 board is given. Ref. 28's wormhole + billiard-ball construction handles classical PFs. A quantum, coherent version (coherent scatterers in the CTC region) is assumed, not built.
- Whether quantum CTC dynamics is linear (ref. 16) or nonlinear (Deutsch) is unsettled. Our signature is model-dependent.
- The physical meaning of the 22 genuine never-crossed orbits and of non-polytopality is conjectural.


**H.15.6 Audit (Oct 23 2026) [labels as marked].**
- *Script.* code/stochastic/cyclic/embed/embed_check.py (log alongside) [EXACT-CERTIFIED, rational arithmetic]. For the Lugano PF and both H.13.2 sources it computes the signalling structure, the fixed-order test over all 6 orders, and ref. 16's Thm 3 reduced test.
  - Lugano and H.13.2 with phi = (|0>+|1>+|2>)/sqrt3: every party signals to every other, there is no first party, and the process is not fixed-order.
  - H.13.2 with phi = (|0>+|1>+|2>-|5>)/2: pairwise signalling is A->C, B->A, B->C and C->A; B is marginally first with p(i_B) = (3/4, 1/4); the process is not fixed-order. 32 conditional A-C loops are invalid, as Theorem H.2 requires.
  - Ref. 16's Thm 3 test fails for both H.13.2 sources and passes for Lugano. This is diagnostic only, since mixtures of PFs can also fail it.
- *Explicit region assignment (phi_A source) [INTERPRETIVE, from VR Defs 20-24 + script].*
  - B gets a single localised region in the common past of A and C.
  - A and C cannot both be localised: by VR Thm 4 applied to the A-C signalling cycle at fixed o_B, at least one of them needs a delocalised input region.
  - The source must also reach B's past, because the A-C loop is valid only together with i_B.
  - For the symmetric source and for Lugano, all three agents' in/outputs must be non-localised (VR Cor 1).
- *What holds per object.*
  - Switchboard (H.12), rational 4-term counterexample (H.13.2) and Z8 boards: valid processes in ref. 15's 710,760-vertex polytope, outside conv(PF) [PROVED / EXACT-CERTIFIED]. So they are fine-tuned classical processes in ref. 15's sense, realised by reversible quantum loops. Ref. 16 notes that such processes need not have classical reversible extensions.
  - Tuned and generic ≤3-term boards: wherever proved PF blends (H.17.9, H.17.13, H.17.14, part of H.17.15), they are classically CTC-realisable as mixtures [PROVED + CITED]. The ≥4-class cases are OPEN.
  - Continuous or measurable PFs (F.5): ref. 16's Thm 1 holds for continuous variables, as stated in ref. 16, and its Eq. 7-8 is a continuous Lugano example; Thm 2's T^e(i) = i + e works on any group, and F.5's measure preservation is its measure-theoretic form. The classical CTC embedding therefore extends [CITED + PROVED]. The quantum lift on L² is proved only in F.5's cases; in general it is OPEN.
  - Countable ℓ² operators (Lean induced_unitary_l2 and valid_*_l2): the lift is a unitary process, and ref. 16's classical framework covers countable sets.
  - VR's no-go and fine-graining theorems are proved only for finite-dimensional systems and finite partitions. Their extension to ℓ² or L² processes is OPEN [not claimed].
- *Corrected.* (i) The H.15.1 wording on ref. 15's polytope. (ii) "Fine-grained explanation must be quantum" is downgraded to OPEN. (iii) The H.15.3 item 3 spacetime reading is limited to operator level. (iv) VR theorem numbers, erratum and PRL companion are added. (v) The 3+1 question is now answered by Grothus-Vilasini. (vi) Item 5 is updated to H.17. (vii) The Paunković-Vojinović journal reference is added.
- *Checked, no change needed:* ref. 16 Thms 1-3, Sec. VII and CQG 36, 224002; ref. 17 Thm 2 and Sec. 7 (Lugano counterexample; Thm 2 is stated bipartite with a "straightforward" multipartite generalisation); ref. 28 authors and arXiv number. Ref. 28's journal reference (CQG 37, 205011) was not re-fetched.
- *Open.* (a) Is every H.12 or H.13.2 board a routed circuit in the sense of Vanrietvelde et al.? Our boards are concrete test cases for their conjecture. (b) Is there a classical fine-grained VR realisation of p? (Answered in part by H.15.7: not with single-use agents.) (c) VR-type theorems in infinite dimensions. (d) The ≥4-class H.17 boards.

**H.15.7 Two open problems from H.15.6, pushed (Oct 23 2026) [labels per item].**

*(B) Can a finer-grained causally ordered model reproduce p?*
- **Setting.** Each coarse agent k applies its local operation exactly once per run. It acts at one fine-grained location (its "active slot"); at every other location it receives "vacuum", and its action on vacuum is fixed and does not depend on its choice. Agents' outputs are free settings, independent of all hidden variables. The fine-grained network is acyclic: fixed order, or order chosen dynamically by classical values, with any number of extra non-agent nodes and hidden variables. This is the set-up assumption of VR (Sec. IX) and of Salzger-Vilasini, in classical form.
- **Lemma H.15.7a [PROVED].** Under these assumptions, with classical carriers, the coarse correlations P(i|o) are causal correlations: mixtures of dynamically ordered deterministic strategies. Proof: fix the hidden variables. Acyclicity orders the active slots, and the first active slot's input depends only on the hidden variables. Inductively, each agent's input is a function of the earlier agents' settings, so P(i|o) is a point of the dynamic-order causal polytope. Averaging over hidden variables keeps it there. With quantum carriers and quantum control of order (QC-QCs, which also use each operation once), the same conclusion is a theorem of Wechs, Dourdent, Abbott and Branciard (arXiv:2101.08796, PRX Quantum 2, 030335 (2021); erratum PRX Quantum 4, 030901 (2023) on Prop. 7, conclusion unaffected) [CITED].
- **Theorem H.15.7b [PROVED; exact certificate].**
  - The test uses a legal local operation: each agent measures its input as the outcome and emits a free bit o_k as the setting.
  - With these operations, the H.13.2 correlation violates a causal inequality, for both sources. Code: code/stochastic/cyclic/embed/finegrain_check.py, which enumerates all 138,304 deterministic dynamically ordered strategies.
  - An LP plus a rational Farkas vector y, checked exactly, gives min over causal strategies of y·P = 0, while y·p = -5/4 (φ_A) and -4/3 (φ_B). As a control, Lugano gives -4.
  - **Hence no model of the kind in Lemma H.15.7a, classical or QC-QC, reproduces H.13.2.** In particular the board W is not a QC-QC, so Salzger-Vilasini's QC-QC-to-causal-box construction does not apply to it.
- **Consequence for VR [CITED + PROVED].** VR's Thm 5 says that any relativistically causal fixed-spacetime realisation has a fine-grained fixed-order explanation with M ≥ N "possibly communicating" agents. For H.13.2, that explanation must break the single-use set-up: some coarse agent's operation is not realised as one application at one active slot.
- **The H.12 switchboard is not settled.** At this level of operations its correlation is causal: the LP is feasible, in floating point [NUMERICAL]. Whether another instrument witnesses a causal-inequality violation is OPEN; conv(PF)-exclusion alone does not imply it.
- **OPEN.** Is there any classical fine-grained model that allows multiple use or communicating sub-agents, as in VR Thm 5, for H.13.2? Lemma H.15.7a shows such a model must violate single use.

*(A) Are the boards routed quantum circuits?*
- **Precise statements [CITED, arXiv:2206.10042v3].**
  - Vanrietvelde, Ormrod, Kristjánsson and Barrett (Quantum 9, 1923 (2025)): a routed graph is valid if it is bi-univocal and its branch graph has no strong loops (Sec. 2.4). Any process obtained by "fleshing out" a valid routed graph is consistent.
  - **Conjecture 1:** any unitary process, hence any unitarily extendible one, can be obtained by fleshing out a valid routed graph.
  - **Conjecture 2:** the skeletal supermap violates causal inequalities iff its branch graph has (necessarily weak) loops.
  - Their footnote 21: the framework "provides no way to infer the routed circuit decomposition of a given process". Lugano is reconstructed (Sec. 4.3, Fig. 27) with an ad hoc vote-counting node X and computational-value indices.
- **Computation [EXACT/NUMERICAL, code/stochastic/cyclic/embed/routes_check.py].** For the purifications V: |o>|s> -> Σ_i U_o[i,s] |i>|o>:
  - Lugano: the station route (o, s) -> i is a function (univocal, support 1).
  - H.12: every column has support 8.
  - H.13.2: columns have support 1 or 4.
  - So the computational-value sectorisation that makes Lugano's station univocal gives equivocal routes for our boards. VOKB's Lugano graph does not transfer directly.
  - In the Fourier sectorisation (medium indexed by z), all three are diagonal, and o enters only as a phase. For Lugano the phase is the character (-1)^{z·w(o)}; for H.13.2 it is (-1)^{m_o(z)/2}; for H.12 it is i^{m_o(z)}. Non-character phases are exactly what puts the boards outside conv(PF) (X-type boards, H.10).
- **Status.** Pure boards are unitary processes, so Conjecture 1 predicts routed decompositions for H.12 and H.13.2 [CITED prediction]. Conjecture 2 together with Theorem H.15.7b predicts that any routed graph for H.13.2 has weak loops in its branch graph [conditional]. No explicit valid routed graph is given here, and no obstruction is proved: **OPEN**. Our boards are concrete test cases: an obstruction would refute Conjecture 1, and a decomposition would give the first routed circuit outside conv(PF). A natural candidate (INTERPRETIVE) is a station node indexed by Fourier sectors z, applying an o-controlled phase oracle, with agents connected through Hadamard-type routes. It is checked against the formal Sec. 3 rules in H.15.7c below: it fails.

**H.15.7c Follow-up (Oct 23 2026, second pass).**
- **The Fourier-station candidate fails VOKB's Principle 2 [EXACT; code/stochastic/cyclic/embed/rg_check.py, rg_check.log].**
  - The checker is a brute-force implementation of VOKB Defs 3.1–3.7 and Principles 1–2 (arXiv:2206.10042v3). It computes the choice relation and its adjoint, bi-univocality, solid/green/red branch-graph arrows, and a search for non-weak loops. Calibrations: a sectorised wire A → B is valid; an unindexed A ⇄ B loop is invalid.
  - **Candidate graph.** Source S with output P indexed by z ∈ {0,1}^3 (one-dimensional sectors), fleshed out by Hd·φ. Station Φ with inputs o_A, o_B, o_C (one-dimensional sectors) and z, and route (o, z) ↦ z. Output M indexed by z goes to a node D (fleshed out by Hd), whose unindexed qubit wires go to A, B and C. Global output F.
  - **Fleshing out.** Φ = Σ_o |o><o| ⊗ diag((-1)^{m_o(z)/2}) follows the route, and D·Φ·S gives exactly the H.13.2 unitary (exact check). With the phases replaced, the same holds for H.12, Z8 and Lugano.
  - **Bi-univocality holds in both directions.** Branches: Φ has 8 (Φ^z), every other node has 1.
  - **Weak loops fail**, for example on the loop A^0 →(solid) Φ^z →(red dashed) D^0 →(solid) A^0. The solid arrow A → Φ^z exists because o_A is not fixed by Φ's branch. The red arrow exists because D's adjoint choice of z fixes which Φ^z happens.
  - **Variant.** Recording o on an internal indexed wire gives Φ 64 branches Φ^{o,z}. It is still bi-univocal and still fails weak loops: the solid arrow becomes green, giving the loop A →(green) Φ^{o,z} →(red) D →(solid) A, which is mixed and so not weak.
  - **This is not an obstruction to all decompositions.** The routes, and therefore the verdict, do not depend on the phases. The same graph with Lugano's character phases is equally invalid, yet Lugano has a valid routed graph (VOKB Fig. 27, which uses computational-value indices). The failure belongs to this sectorisation, not to the boards.
  - **What Conjecture 2 says.** It only constrains valid graphs, so this candidate tells it nothing. Conjecture 1, Conjecture 2 and Theorem H.15.7b together predict that a valid routed graph for H.13.2 exists and that its branch graph has weak loops, all green or all red [conditional].
  - An explicit valid graph, or an obstruction to all graphs, remains **OPEN**. Note that the agent wires would have to carry non-trivial sectors, since unindexed agent inputs give solid arrows into the agents.
- **H.12: local-instrument search finds no violation [NUMERICAL; code/stochastic/cyclic/embed/instr_search.py, instr_h12_s2.log].**
  - **Family searched.** Per agent and per setting x: a projective measurement of the input qubit along one of 13 distinct Bloch directions (θ ∈ {0, π/4, π/2, 3π/4}, φ ∈ {0, π/4, π/2, 3π/4}), outcome a = b, and output encoding o = g_x(b) ∈ {0, 1, b, 1 − b}. This covers adaptive outputs. The search used 150 random instruments plus 150 steps of continuous-angle hill climbing.
  - **Robustness LP.** max t such that t·P + (1 − t)·uniform is causal, over the 138,304 deterministic causal strategies.
  - **Result for H.12:** best t = 1.000000. So no violation was found, but the optimum sits on the boundary of the causal polytope.
  - **Control:** H.13.2 φ_A reaches t = 0.6963, a violation.
  - A second seed did not finish (no output).
  - **Z8 class 10515** with the H.14.2 source: best t = 1.000017, no violation found [NUMERICAL, instr_z8.log]. Its computational-basis station routes have support sizes {1, 4, 5, 6} (not univocal), and it is Fourier-diagonal (routes_check.log).
  - **Status.** This narrows but does not settle the question. It is OPEN whether any instrument (general POVMs, entangling the agent's input with a memory, more settings) shows that H.12 or Z8 violates a causal inequality. If none does, H.12 would be a pure non-PF board whose correlations are all causal. Even then, it would still be excluded from single-use classical models with deterministic local operations, because p ∉ conv(PF) (H.12). The fixed-instrument test is weaker than PF-membership.

### H.16 Round 10 status (Oct 23 2026) [proved in Lean unless marked]
- **Unitarity closed.** The H.12.3 gap "isometry, not unitary, for infinite ancillas" is now closed. `isUnitaryInf_Vsb` proves the Switchboard loop is unitary against every family of countable ancillas. `purification_conjecture_false_unitaryInf` then gives the counterexample in the unitary form. The proof checks row orthonormality (`row_scalar_key`, an exact kernel check) and shows that an isometry with orthonormal rows is onto.
- **Validity link, partial.** `valid_pfPoint_iff` proves `Valid (pfPoint w) ↔ IsPF w`, and `validWith_of_valid_pfPoint` links this to `PFUL.ValidWith`. Both hold only for deterministic w. `ValidWith` is not defined for non-deterministic processes such as `pcl`.
- **F.5.5 for general point maps.** `PFUL.Continuous.closedLoop_general_unitary` covers measurable bijections with a positive density. `closedLoop_jacobian_unitary` covers global bijections of ℝⁿ with an invertible derivative, where the density is |det g'|. Round 11 update: `closedLoop_jacobian_unitary_ae` covers bijections that are differentiable off a null set, with det g' ≠ 0 a.e. (piecewise-smooth maps); `closedLoop_jacobian_isometry` gives an isometry when the Jacobian may vanish (not onto if it vanishes on positive measure). Non-injective local diffeomorphisms are not point-map unitaries.
- **Round 11: automatic boundedness and ancillas of any cardinality [PROVED, Lean].** A kernel with orthonormal rows and columns over any index set is the matrix of a bounded unitary of ℓ² (`PFUL.Counterexample.unitary_of_unitaryKernel`). The Switchboard loop is unitary for local operations given only as unitary kernels, with ancillas of any cardinality (`isUnitaryKer_Vsb`), hence for bounded unitaries on non-separable ℓ²(κ) (`isUnitaryAll_Vsb`, `IsUnitaryInf` without `Countable`), and `purification_conjecture_false_unitaryKer` is the strongest form of H.12.1. For process functions on groups of any cardinality, ψ ↦ φ·(ψ∘τ) is a unitary of ℓ² with no measurability, countability or boundedness hypothesis (`PFUL.LiftAuto.closedLoop_l2_unitary`, `permPhaseUnitary`). Not covered: general unitaries for the lift on uncountable alphabets beyond point maps, and the ℓ²-to-Lean link for automatic boundedness of positive trace-preserving maps (H.16 Round 9 gap, unchanged).
- **Open.** The non-X 3-term boards (from H.14) and the 23 never-crossed inequalities (J.1) were not attacked this round and are still open. (H.17.5 later showed that orbit 92 is positivity, so 22 are genuine.)

### H.17 Non-X three-term boards, local rotations, and what validity alone gives (Oct 23 2026) [labels: PROVED / EXACT-CERTIFIED / NUMERICAL / OPEN per item]

This round attacked the two items H.16 left open: boards that are not of the X type, and the 23 never-crossed orbits of J.1. One of these, orbit 92, turns out to be positivity (H.17.5), leaving 22 genuine. Code and logs are in code/stochastic/cyclic/switchboard/h16/ (scripts csp2, rsearch, z16sample, xcont) and h17/ (struct3, search3, nsearch, nsearch2, pairlemma, siglemma, sigsearch, locrot, locopt, validlp, validcert, shpcheck). Model: a board with at most 3 Pauli terms per outcome is U_o = P_o V_k^σ. Here V_k is 1, α+iβA, or α+i(βA+γB) with A and B anticommuting, and σ flips the signs of β and γ. This is the H.14 form P·exp(i t(cos φ A + sin φ B)). A board is *hard* if it is complete and admissible (unitary and obeying the Pauli rule H.8.1), has a genuine 3-term class, and has no operator-first and no operator-last party. Hard boards are the ones H.6 and H.1 do not already reduce to PF blends.

**H.17.1 Pure non-X three-term boards exist; none leaves the PF hull [NUMERICAL].**
- *Generic parameters* (csp2 structure model, rsearch): 5 seeds × 8,000 complete structures gave 6,551 hard boards. The largest violation of any of the 29,344 hull facets, over all source states, was 5.9·10⁻¹⁵. The largest unitarity or Pauli-rule residual was 4.4·10⁻¹⁶. search3 (6 seeds) gave about 4,200 more hard boards. The best value there was 6.3·10⁻¹⁵.
- *Tuned (non-generic) parameters* (nsearch, nsearch2): here class parameters are chosen so that products U_oU_q† lose terms, which can only happen when the groups ⟨A,B⟩ and ⟨A′,B′⟩ intersect. Supports are recomputed from the matrices, so every cancellation is seen by the Pauli rule. nsearch (3 seeds) gave about 4,600 hard boards. nsearch2 (seeds 1–3 and 11–14; new classes get the most general linear repair) gave 6,340 hard boards. No run printed VIOLATION (threshold 10⁻⁶). The best facet value was ≤ 6.4·10⁻¹⁵ and the Pauli-rule residual was ≤ 6·10⁻³¹.
- *Conclusion.* Pure boards that are not of the X type and have ≤3 terms per outcome do exist, and in large numbers. Every one tested lies inside the PF hull to round-off. Whether every such board is a PF blend is **OPEN**. H.14.1 proves this only for X-type boards.

**H.17.2 Support transport (SH) [definition; reduction OPEN].** SH says: for every pair o≠q with D=o⊕q, every X-shadow x(P_o)⊕x(P_q)⊕t⊕t′ (with t and t′ ranging over {0}∪X-parts of the class generators) obeys the X-type Pauli rule (x∧D)≠D. Two coarser variants were also checked. SH⁺ groups o~q when U_oU_q† is monomial (all of its terms share one X-part). SH⁺⁺ first absorbs a common right factor U_r† into the source state. The hoped-for reduction is "SH (or SH⁺⁺) ⇒ the H.14.1 X-type argument applies ⇒ PF blend". That reduction is not written out or proved here and remains **OPEN**.

**H.17.3 SH can fail for a pair but not for an admissible generic cube [PROVED by exhaustive exact enumeration, generic-support model].**
- pairlemma (exhaustive, exact F₂ arithmetic): it covers all anticommuting pairs (A,B), sign changes Δσ∈{1,2,3}, translations R=P_o⊕P_q and differences D≠0. Of these, 94,365 are pairwise admissible. SH fails in 16,344 of them, so SH is *not* automatic pair by pair.
- siglemma (sign-variant lemma): for each of the 16,344 SH-failing pairs, it searches the intermediate cube vertices for a completion. For |D|=2 this means a common neighbour. For |D|=3 it means a path o–m₁–m₂–q with all six pairwise constraints. Same-class intermediates are enumerated over all 4·64 options. For other-class intermediates only necessary edge conditions are imposed (an over-approximation, so "infeasible" is a proof). 432 configurations survive the local test, and **0** extend to the full cube.
- *Scope.* The statement covers same-class type-3 sign-variant pairs in the *generic-support* model: a board with generic parameters whose only SH failures would come from sign variants of one class cannot be admissible. It says nothing about tuned parameters. sigsearch agrees: of 60,000 structures, 4,098 contain sign variants and 59 are hard, and none fails SH.

**H.17.4 Tuned boards do violate SH, but not SH⁺⁺, and stay in the hull [NUMERICAL].** With tuned parameters the conservative SH test failed on 35 hard boards across the nsearch2 seeds. The best facet value among them was 5.9·10⁻¹⁵, so none is a violation. Only one board failed SH⁺ (seed 11, board 3339, saved as shp_11_3339.npy). It fails SH⁺ on 6 pairs and satisfies SH⁺⁺ for a suitable common right factor (0 bad pairs; shpcheck.log). Seeds 12–14 had no SH⁺ failures. *Every hard board found satisfies SH⁺⁺* [NUMERICAL]. A proof that SH⁺⁺ always holds is **OPEN**.

**H.17.5 What validity alone gives on the facets [EXACT-CERTIFIED for 22 orbits; PROVED for orbit 92].** Let Valid be the polytope of p(i|o) ≥ 0, normalised, such that every deterministic local intervention has fixed-point probability 1. The validity equalities have rank 27, so Valid has affine dimension 37. Purif ⊆ Valid.
- *Exact certificates* (validcert): for each of the 22 never-crossed orbits other than 92 there is an exact rational point of Valid where the facet functional is negative. The functional is rationalised and checked to reproduce the integer facet values on all 744 PFs. The relative values are −2/9 for orbits 4–11, 14 and 25, and −1/6 for orbits 26, 28, 30, 31, 53, 54, 57, 66, 69, 75, 79 and 81. So validity alone does not imply these 22 inequalities. Any proof that they hold on Purif must use purity [EXACT-CERTIFIED].
- *LP screen over all 93 orbits* (validlp): 92 of the 93 facet orbits have strictly negative LP minimum on Valid (relative values between −1/3 and −1/6). For orbit 92 the minimum is 0.
- *Orbit 92 is just positivity [PROVED, exact dual certificate; cert92.py, cert92.log].* The orbit-92 representative (facet 6928) has range 1 on the PFs and g₀=1/16. Exact rational multipliers y were found for the 72 validity equalities (normalisation and fixed-point equalities, denominators ≤128). They satisfy g − Aᵀy = e_(111|000) and g₀ + b·y = 0 exactly in Fractions. Hence **on all of Valid the orbit-92 functional equals p(111|000)**, which is ≥ 0 for every process. Consequences:
  - The minimisers on Valid are exactly the valid processes with p(111|000)=0. This face has dimension 36 (dim Valid = 37), and no coordinate vanishes identically on Valid. So the face is a facet of Valid, namely the positivity facet p(111|000) ≥ 0.
  - 651 of the 744 PFs lie on it.
  - Orbit 92 (64 facets) is the orbit of the 64 positivity facets p(i|o) ≥ 0. J.1's representative already reads p(111|000) ≥ 0.
  - It holds for every classical process, purifiable or not. It was never a genuine open inequality. **The never-crossed open list is therefore the 22 orbits 4–11, 14, 25, 26, 28, 30, 31, 53, 54, 57, 66, 69, 75, 79, 81.** Every one of these is violated somewhere on Valid at an exact rational point, so a proof that they hold on Purif needs purity.

**H.17.6 The 22 genuine orbits (and orbit 92) under wider board families [NUMERICAL].** None of the following produced a violation.
- *Z₁₆ X-type boards* (z16sample): 2 runs, more than 5,500 sampled pure boards each, scored on every facet of the 23 orbits. The best value was 3.9·10⁻¹⁵.
- *Continuous X-type phases* (xcont): the violation was maximised with a penalty on the Pauli-rule residual, starting from the best Z₈ boards. The largest values were 2.3·10⁻⁷ (orbit 25, residual 3·10⁻¹¹), 3·10⁻⁸ (orbit 92, which is positivity by H.17.5, so this value is purely an artefact) and ≤ 10⁻⁸ for the others. These are consistent with penalty/round-off artefacts, below the 10⁻⁶ threshold for exact certification, and were not pursued.
- *Local rotations* L=L_A⊗L_B⊗L_C applied on the left. These preserve the Pauli rule exactly, so every L·U is pure, but p changes. locrot tried the 216 local Clifford cosets on all 193 Z₄ classes (2 runs) and got a best value of 4.4·10⁻¹⁵. locopt optimised continuously over SU(2)³ from Z₄ starts (2 runs) and got a best value of 3.6·10⁻¹⁵.

**H.17.8 Proof attempt: support transport implies PF blend [PROVED: Pauli coset-transport theorem; GAP: shadow versus group closure; local-Clifford reduction does not work].**

*(a) Pauli coset-transport theorem [PROVED].* Let U_o = P_o G_{κ(o)}, where P_o is a Pauli string with X-part a(o) (any Z-part and phase), κ partitions the outputs into classes, and the Pauli support of G_κ has all its X-parts in a subgroup H_κ ≤ F₂³ (Z-parts arbitrary). Suppose every class-constant selection o ↦ a(o) ⊕ h_{κ(o)}, with h_κ ∈ H_κ, is a PF. Then p_φ ∈ conv(PF) for every source state φ.
*Proof.* A Pauli X^h Z^z with h ∈ H_κ maps each |j⟩ into the coset j+H_κ, so G_κ is block-diagonal on the cosets of H_κ and unitary on each block. The left factor P_o only permutes basis states by a(o) and multiplies by phases, so p(j⊕a(o)|o) = |(G_κ φ)_j|² =: r_κ(j). From here the proof of H.10.6 goes through word for word: μ and r_κ have equal mass on every coset, so the transport plans π_κ exist, and the same weights λ give p. ∎
Sign variants cause no difficulty. V^σ is a different unitary with the same X-support, so (k,σ) is simply a different class with the same H_κ. Z-components cause no difficulty either: they are diagonal.

*(b) Reduction to a support condition [PROVED].* By H.10.3 (pairwise exclusivity ⇔ PF, exhaustive and exact), the hypothesis of (a) is equivalent to the following condition, called **SH_grp**: for every pair o≠q in different classes, with D = o⊕q, every X-string a(o)⊕a(q)⊕h⊕h′ (h ∈ H_{κ(o)}, h′ ∈ H_{κ(q)}) satisfies (x ∧ D) ≠ D. Same-class pairs need nothing. There K_{oq} = P_oP_q† is a single Pauli string, and the Pauli rule (H.8.1) already forbids it from having an X-part covering D. So **SH_grp ⇒ PF blend for every φ.** This holds with no restriction on the number of terms. For an X-type ≤3-term board (two-term classes, H_κ = {0,d}) SH_grp is exactly what H.14.1(b) verifies, so H.14.1(b) is the special case.

*(c) The gap [OPEN].* SH as tested in H.17.2–H.17.4 uses the shadow T_κ = {0} ∪ {x(g) : g a generator of class κ}. For a 3-term class V = α + i(βA+γB) this is {0, x_A, x_B}, and H_κ = ⟨x_A, x_B⟩ also contains x_A⊕x_B. The Pauli rule controls only strings that actually occur in K_{oq} = U_oU_q†. Across two different generic classes these strings have X-parts a⊕a′⊕{0,x_A,x_B}⊕{0,x_{A′},x_{B′}}. The term x_A⊕x_B (because AB never occurs in V) and its translates are not controlled. So SH implies SH_grp only when x_A⊕x_B is already in T_κ, or when the extra strings happen to be allowed.
- When x_A = 0 or x_B = 0 (one generator is a Z-string) or x_A = x_B, H_κ = T_κ up to {0} and there is no gap.
- In the remaining case (x_A, x_B, x_A⊕x_B all nonzero and distinct) the gap is real.
SH⁺⁺ (common right factor absorbed into φ) has the same gap. Closing it needs either an exhaustive exact check that SH_grp holds on every admissible ≤3-term cube in the struct3 model (an F₂ enumeration of the pairlemma/siglemma kind, not done this round), or a different transport for non-group shadows. *Time-boxed sample [exact per structure; sample NUMERICAL] (shgrp.py, shgrp_1.log).* struct3 drew 77,211 random admissible structures in the generic-support model, 80 s, seed 1. Of these, 11,491 are hard, and 7,801 of the hard ones contain a class whose gap is real (|⟨x_A,x_B⟩| = 4). SH_grp failed for **0** of them. Admissibility and SH_grp are exact F₂ tests, so by (a)–(b) each sampled structure is **proved** to give PF blends for generic parameters. What remains open is that *every* structure does: the sample is not exhaustive and tuned (non-generic) parameters are not covered. Status: **OPEN; reduced to a finite F₂ enumeration (csp2/struct3 model plus SH_grp), with no counterexample in 11,491 hard samples**. *Update:* the enumeration was completed in H.17.9, and SH_grp holds on every admissible generic board.

*(d) Local Clifford conjugation does not reduce to the X-type case [observation].* A local Clifford C maps Paulis to Paulis and preserves the Pauli rule. But replacing U_o by C U_o C† changes p unless C is diagonal up to a permutation in the computational basis. On one qubit such C (generated by X, Z, S) map X-type strings to X- or Y-type ones and never map Z to X. Conjugation therefore cannot remove the Z-components of A or B while preserving p. For p only the X-parts matter (part (a)), so the reduction actually available is the one in (a)–(b), and the X-type proof extends exactly as far as SH_grp holds.

**H.17.9 Exhaustive exact check of SH_grp in the generic model (Oct 23 2026) [PROVED by exhaustive exact enumeration, generic-support model] (shgrp_exh.py, shgrp_local.py, shgrp_cube.py, shgrp_dfs.py; .log/.json alongside).** The enumeration covers 1,072 class options: V=1, 63 two-term classes, and 1,008 anticommuting pairs A<B. It includes pairs of distinct classes with identical generators. It runs over every left-Pauli difference R (64) and every D≠0 (7).
- *Pairwise (shgrp_exh).* There are 1,999,627 pairwise-admissible different-class configurations, using the generic support R+{0,A,B}+{0,A′,B′}. **SH_grp fails pairwise in 329,280 of them.** Among the 98,685 admissible sign-variant configurations it fails in 16,344. So pairwise admissibility does *not* imply SH_grp, and a cube-level argument is needed. A typical failure: c = (V=1), c′ = (X₂, X₁Z₂), R = Z₂, D = parties {1,2}. The three support strings Z₂, Y₂, X₁ are allowed, but x(R)⊕x_A⊕x_B = X₁X₂ covers D.
- *Sign variants.* For a sign variant with flips on both generators the support is {0,A,B}, so SH and SH_grp coincide on these pairs (the same 16,344 cases as pairlemma). By the sign-variant lemma H.17.3 **none** of them completes to an admissible cube [PROVED, generic model].
- *Different classes, |D|=1 and |D|=2 [PROVED, generic model].* Across a cube edge of party p, every term of K must be trivial on p. Between different classes this forces all generators of both classes to be trivial on p. There are no failures with |D|=1, and the 52,416 with |D|=2 all fail the necessary common-neighbour test (shgrp_local: 0 survive). The cube test below confirms this.
- *Different classes, all D (shgrp_cube).* Fix o=0 and q=D, and give each other vertex a label in {class of o, class of q, fresh identity class}. This over-approximates: sign variants are merged and R and all non-edge constraints are ignored. Then require the edge condition on all 12 cube edges. Of the 329,280 failures, **329,192 are proved impossible**. **288, all with |D|=3, survive** this coarse test. In every one of them o carries the identity class V=1 and q a 3-term class, with 2 values of R per class pair. They are written to shgrp_cube_survivors.json.
- *The 288 survivors: exact cube search (shgrp_dfs.py, shgrp_dfs.log).* By a global left Pauli and a relabelling of the base sign of q's class we may take o=0 with P_0=1 and q=7 with P_7=R and σ=0. Every other vertex m ranges over all states (P_m, class k among all 1,072 options, σ). A pair of states is accepted if the different-class generic support, or (when the two states share a class) the same-class support R+S(ds), satisfies the Pauli rule H.8.1 for their D. Allowing both readings over-approximates admissibility, so an empty result is a proof. Domains are filtered against o and q, then made arc-consistent over all 28 pairwise constraints, then searched by DFS. **In all 288 cases no cube exists**: after arc consistency the domain of vertex 1 is empty (25 s in total). A sanity run (shgrp_dfs_sanity.py/.log) checked that the pair test accepts all 28 pairs of each of 300 random admissible struct3 cubes, including cubes with 2–4 classes (300/300 accepted).
- *Status.* **Theorem: every admissible board with ≤3 Pauli terms per outcome and generic parameters satisfies SH_grp, hence (H.17.8) is a PF blend for every source state.** The scope is the generic-support model of struct3: U_o = P_o V^σ, and the support of every U_oU_q† is the generic one, with no cancellations. The theorem covers non-X boards; X-type boards were already covered by H.14.1. The chain is: different-class |D|≤2 failures excluded locally; sign-variant failures excluded by H.17.3; 329,192 |D|=3 failures excluded by shgrp_cube; the last 288 excluded by shgrp_dfs. This is consistent with the random sample of H.17.8(c) (11,491 hard cubes, 0 SH_grp failures). **Tuned parameters are not covered** (H.17.10).

**H.17.10 Tuned (non-generic) parameters [analysis; OPEN].** Genericity can fail in three ways.
- (i) *Degenerate coefficients* (β=0 or γ=0). These lower the term count, so the board is covered by the same model with a smaller class.
- (ii) *Proportional classes* (G_c ∝ G_{c′}). The classes simply merge, and the same-class pairs need nothing (H.17.8b).
- (iii) *Cancellation in U_oU_q†.* This needs coinciding products, so the groups ⟨A,B⟩ and ⟨A′,B′⟩ must intersect, and coefficients tuned to cancel. Cancellation *removes* strings from the support, so it makes more structures admissible. SH_grp itself depends only on R and the generators' X-parts, not on the coefficients. Consequently:
  - H.17.8(a)–(b) apply verbatim to any tuned board that satisfies SH_grp.
  - What can go wrong is only that a tuned board is admissible although its generic counterpart is not, and fails SH_grp.
- *Evidence.* nsearch2 found 37 hard boards with a tuned cancellation, and 35 of them fail the weaker SH test. All are inside the PF hull to 6·10⁻¹⁵. *SH_grp on these boards [EXACT per board] (shgrp_tuned.py, shgrp_tuned.log).* All 37 structures (P_o, class labels, generators) are saved in ns2_*.json. nsearch2 reuses a class only with the identical V, so the class partition is exact, and SH_grp depends only on these integers. **The same 35 fail SH_grp** (the 2 that pass SH also pass SH_grp, so they are proved PF blends). Every one of the 37 has two classes whose generator X-parts span the same group H (36 with two 3-term classes, 13 of those with identical generators but different coefficients). So tuned cancellation really does produce admissible boards outside the SH_grp route, as anticipated in (iii). These 35 boards are numerically in the PF hull and satisfy SH⁺⁺ (H.17.4), but no proof covers them [OPEN]. Their unitaries were not saved (except shp_11_3339.npy), so exact facet tests were not possible this round.
- *Proof strategy.* A proof for tuned boards would enumerate the finitely many cancellation patterns: which products of {1,A,B}·{1,A′,B′} coincide and can cancel. Each pattern gives a modified support. Rerunning shgrp_exh/shgrp_cube on the modified supports would settle the tuned case.

**H.17.11 Tuned boards: right-absorption transport (Oct 23 2026) [theorem PROVED; per-board checks NUMERICAL supports, exact F₂ test] (nsearch2b.py, tbcheck.py, tbcheck.log, tb_*.npz).**

*(a) Theorem (right-absorbed coset transport) [PROVED].* Fix any output r and set W_o = U_oU_r†. Group o~q when W_oW_q† is monomial (a permutation by one X-string times a diagonal unitary). In each group pick a representative ρ, put G_ρ = W_ρ, M_o = W_oW_ρ† (monomial, X-part a(o)), and let H_ρ be the group generated by the X-parts of the Pauli support of G_ρ. Define **SH_grp^r**: for every pair o,q in different groups with D = o⊕q, no X-string a(o)⊕a(q)⊕h⊕h′ (h ∈ H_{ρ(o)}, h′ ∈ H_{ρ(q)}) covers D. If SH_grp^r holds for some r, then p_φ ∈ conv(PF) for every source state φ.
*Proof.* p_φ(i|o) = |⟨i|W_o ψ⟩|² with ψ = U_rφ. As φ ranges over all states, so does ψ. W_o = M_oG_{ρ(o)}, and the proof of H.17.8(a) uses only that the left factor maps each basis state to one basis state shifted by a(o), up to a phase. A monomial does exactly that, so H.17.8(a) applies to (W, ψ). Its hypothesis is that every group-constant selection is a PF. By H.10.3 this is pairwise exclusivity. Pairs in different groups are covered by SH_grp^r. For a pair in one group, W_oW_q† = U_oU_q† is a nonzero monomial with X-part a(o)⊕a(q). If that X-part covered D, every term of U_oU_q† would be forbidden by H.8.1, which is impossible. ∎
This contains H.17.8 (take r in any class and note V_c V_c† = 1). It also contains SH⁺⁺ upgraded to the group closure. The case where two classes share one group H is exactly where it helps: W = V′V† lies in the algebra spanned by the Paulis with X-parts in H, and tuned cancellation shrinks its support.

*(b) Regenerated tuned boards [NUMERICAL supports; exact F₂ test; facets and LP high-precision].* nsearch2b is nsearch2 with every tuned-cancellation board saved: U, (P_o, class, generators) and the worst-case source state of its tightest facet. Six bounded runs (seeds 21–26, 420 s each) gave 18 tuned hard boards. **All 18 fail SH_grp**, with 1–8 bad pairs; shp_11_3339 was added as a 19th. Results:
- **SH_grp^r holds for all 19** (r = output 0 suffices). For 13 of them all W_o are monomial: one group, so V′ is a monomial times V and the classes merge outright. For the other 6 there are two groups, {monomial} and one 2-term X-type group with |H| = 2. Given the supports, each of these 19 boards is therefore a **PF blend for every source state** by (a). The supports were read off numerically with tolerance 10⁻⁹; Pauli-rule residuals are ≤ 10⁻³⁰. The F₂ test itself is exact.
- *Facets:* the largest facet value, maximised over source states, is ≤ 5.9·10⁻¹⁵ for every board.
- *Explicit PF-blend decompositions.* For each board, LP over the 744 PFs at the worst-case source state and at 3 random states finds an exact-feasible blend (L1 residual 0 in HiGHS). At the worst-case state 1–9 PFs suffice, so the point lies on a low face; at random states 29–38 PFs are needed. After rounding the weights to rationals with denominator ≤ 10¹² and renormalising, the reconstruction error is ≤ 3·10⁻⁸. The p are irrational, so no exact rational identity is possible. Under (a) the decomposition exists exactly anyway.
- The 35 boards of H.17.10 were not regenerated (their U were never saved), but their structure matches: two classes spanning one H.

*(c) What is still open.* (a) settles any tuned board that passes SH_grp^r, and every tuned board found does. What is not proved is that *every* admissible tuned ≤3-term board satisfies SH_grp^r. A proof would enumerate the cancellation patterns of V′V† inside the group algebra of H (finitely many for |H| ≤ 4) and rerun the shgrp_exh/shgrp_cube/shgrp_dfs pipeline on the resulting supports. That was not done this round [OPEN]. *Conjecture (evidence: 19/19):* in an admissible hard tuned board, absorbing the right factor of one class leaves at most one non-monomial group, and that group is X-type with |H| = 2. The board then reduces to the H.14 X-type situation.

**H.17.12 Cancellation patterns of V′V† and more tuned boards (Oct 23 2026) [partly PROVED, partly NUMERICAL; closure OPEN] (tpat.py, tclass.py/.json, tbcheck.log, tbmerge.py/.log).**

*(a) Coincidence types [EXACT enumeration] (tpat.py).* Take two genuine 3-term classes V = α+i(βA+γB) and V′ = α′+i(β′A′+γ′B′), all coefficients nonzero. Let K = {1,A,B,AB} and K′ be their Klein groups. Over all 1,008² ordered pairs of anticommuting generator pairs, the 9 products {1,A′,B′}·{1,A,B} fall into exactly three types:
- |K∩K′| = 1 (876,960 pairs): all 9 products are distinct, so **no cancellation is possible** [PROVED: each coefficient is a single nonzero product].
- |K∩K′| = 2 (136,080 pairs): 7 strings, two of which collect two products each.
- K = K′ (3,024 pairs): 4 strings with multiplicities (3,2,2,2).

*(b) The same-group case K = K′ [PROVED].* Put I = iA and J = iB. Then 1, I, J, IJ multiply like the quaternions, V = α+βI+γJ, and V′V† = (v·v′) + (terms whose coefficients are the components of v×v′, up to sign) on the strings 1, B, A, AB, with v = (α,β,γ) and v′ = (α′,β′,γ′) unit vectors with all components nonzero. Two components of v×v′ vanishing forces v′ ∥ v, hence all three vanish. v·v′ = 0 and v×v′ = 0 cannot hold together. So the only possible supports of V′V† are:
- {1}, which means V′ = ±V, so the two classes are the same class;
- all 4 strings;
- any 3 of the 4 strings;
- exactly {A,B}, {A,AB} or {B,AB} (v ⊥ v′ together with one vanishing cross component).
tclass.py found exactly these patterns, by explicit construction on 60 instances of the type.

*(c) The |K∩K′| = 2 case and all pairs involving 2-term classes [PROVED by exhaustive exact enumeration] (tcollide.py, tcollide.log).* Every collided string other than those of the K = K′ type has exactly two contributions, φ₁x′_{u′}x̄_u + φ₂x′_{w′}x̄_w. Here x = (α, iβ, iγ), so each x is a real number times a known phase. The string can vanish iff ρ = −φ₁t′_{u′}t̄_u/(φ₂t′_{w′}t̄_w) is real, where the t are those phases. Two strings vanish together iff the two resulting monomial equations in the nonzero reals are sign-consistent. All Pauli phases φ are exact (±1, ±i). Over all 1,071² ordered pairs of 2- and 3-term classes:
- there are no collisions for 3,906 + 60,480 + 60,480 + 876,960 pairs;
- there are 3,024 K = K′ pairs, settled by (b);
- the remaining 63 + 3,024 + 3,024 + 136,080 pairs have exactly two collided strings. **Each of the two can vanish on its own, and never both** (0 exceptions).
For two commuting 2-term classes on the same A, a single cancellation makes V′V† monomial, so the classes merge. This confirms the 60-instance sample of tclass.py.

*(d) More tuned boards (7 more nsearch2b runs, seeds 31–37, 480 s each; 51 boards in total with H.17.11) [NUMERICAL supports; exact F₂ tests].*
- SH_grp fails on 45 of the 51. **SH_grp^r holds on all 51**, so by H.17.11(a) every one of them is a PF blend for every source state.
- The largest facet value is 5.9·10⁻¹⁵. LP PF-blend decompositions were found at 4 source states each, with rational-rounding residual ≤ 3·10⁻⁷.
- *Conjecture of H.17.11(c) [NUMERICAL, 51/51].* After right absorption there is at most one non-monomial group, and it has |H| = 2. 41 boards collapse to one group; 10 have the pattern {monomial, |H|=2}.
- *Where the SH_grp failures come from (tbmerge.log):*
  - In 33 of the 50 saved boards the "tuned" class is V′ = ±V, so V′V† = 1 and nsearch2 simply gave one class two labels. Their SH_grp failures are artefacts of that labelling: the pairs are really same-class pairs.
  - In 8 boards V′V† has 2 terms with one common X-part: a monomial, so the classes merge.
  - In 7 it has 2 terms with two X-parts, which is pattern (b) {A,B}-type or a Z-string pair, |H| = 2.
  - The remaining 2 boards involve 2-term classes.
  - So the genuinely tuned boards found so far all reduce to X-type |H| = 2 after absorption.

*(e) Closure [OPEN].* (a)–(c) give a complete, proved list of the possible pair supports of V′V†:
- generic, when |K∩K′| = 1;
- generic minus exactly one of the two collided strings (or generic), when the groups meet in two elements, including all 2-term cases;
- one of the supports in (b), when K = K′.

The remaining step was not done this round (time-box). It is to rerun shgrp_exh → shgrp_cube → shgrp_dfs with these supports, with each pair of states accepted if any allowed pattern passes the Pauli rule (this ignores consistency across pairs, so it over-approximates), testing SH_grp^r with r ranging over the classes. "Every admissible ≤3-term board is a PF blend" therefore remains **OPEN for tuned parameters**, with no counterexample candidate among 51 tuned boards.

**H.17.13 Tuned closure for two-class boards (Oct 23 2026) [PROVED by exhaustive exact enumeration; over-approximating supports] (tclose2.py, tclose2.log, tclose2_done.txt checkpoint, tclose2_ctrl.py/.log).**

*Theorem.* Let a board have exactly two distinct unitaries up to left Paulis, U_o ∈ {P_oV, P_oV′}, with V and V′ any classes of ≤3 terms: identity, 2-term or 3-term, with any parameters, tuned or generic. If the board is admissible, it is a PF blend for every source state.

*Proof.* Absorb V into the source (H.17.11a): W_o = P_oG^{b(o)} with G = V′V† and b ∈ {0,1}. Admissibility and SH_grp^r then depend only on S = supp(G).
- *Which S occur.* By H.17.12 every possible S is one of three kinds:
  - the generic product support, if there is no collision;
  - generic, or generic minus exactly one collided string, if the collisions have two contributions (proved);
  - any nonempty subset of K, if K = K′. This over-approximates H.17.12(b), which is sound.
- *Normalisation.* Normalised by a left translation, this gives 59,836 non-monomial supports. A monomial S means V′ is a monomial times V; the classes then merge, and the board is a PF blend by H.17.11(a).
- *Reduction to one failing pair.* If SH_grp^r fails at a pair (o,q), use three symmetries: cube translation, a global left Pauli, and G ↔ G† (which has the same support). Together they give o = 0 with state (P = 1, b = 0), and q = D with b = 1 and an h ∈ ⟨X(S)⟩ such that x(P_q)⊕h covers D.
- *Search.* For each S and D, arc consistency plus DFS ran over the remaining six vertices, each with 128 states (P, b). Pair constraints are exact: P⊕P′ allowed when b = b′; every P⊕P′⊕s with s ∈ S allowed when b ≠ b′.
- *Result.* **No admissible board exists in any of the 59,836 × 7 cases** (21 s, 8 cores). Hence SH_grp^r holds and the board is a PF blend. ∎

*Controls.*
- Replacing the failure condition by "any cross pair" makes the same solver find two-class boards for 6 of 300 sampled supports. So the search is not vacuous, and most supports simply admit no genuine two-class board.
- All 7 non-merging two-class tuned boards found by nsearch2b have their S in the enumerated list, and every one of their 28 pairs is accepted by the pair tables.

*Scope.* This covers every board with two classes, tuned or not, including the 7 genuinely tuned two-class boards of H.17.12(d). With H.17.9 it leaves open only boards that have **≥3 distinct classes and at least one tuned class pair**. Only 2 of the 51 tuned boards found are of that kind, and both pass SH_grp^r (H.17.12d). A multi-class version is OPEN: it needs per-class-pair patterns together with a cube search over 1,072-class states.

**H.17.14 Tuned closure for three-class boards containing the identity class (Oct 23 2026) [PROVED by exhaustive exact enumeration; over-approximating supports] (tclose3.py, tclose3_pass1.log, tclose3_pass1_done.txt.gz checkpoint, tclose3_rerun.py/.log, tclose3_cand.py/.log).**

*Refinement of H.17.11(a) [PROVED].* In each group the representative G_ρ may be replaced by Q†G_ρ, where Q is the Pauli string of any one support element s₀. The factor Q is absorbed into the monomials M_o. Then H_ρ = ⟨x ⊕ x(s₀) : x ∈ X(supp G_ρ)⟩, and a(o) shifts by x(s₀). This is the translation normalisation already used in H.17.13.

*Theorem.* Every admissible board whose distinct unitaries (up to left Paulis) are {1, V_a, V_b} is a PF blend for every source state. Here V_a and V_b are any 2- or 3-term classes, and the pair (a,b) may be tuned.

*Proof.*
- *Reduction.* If (a,b) is an untuned pair (K_a∩K_b = {1} and a ≠ b), the board is generic and H.17.9 applies. A board using only two of the three unitaries is covered by H.17.13. Otherwise, absorb the identity class. The pair supports are fixed per class pair and applied to all vertex pairs: supp V_a, supp V_b (which cannot cancel), and S_ab, taken from H.17.12 with "any nonempty subset of K" when K = K′ (sound).
- *Search.* This gives 243,621 jobs (a ≤ b, pattern). A counterexample must fail SH_grp^r for the absorbed identity class at some pair. WLOG (cube translation, global left Pauli) this pair is o = 0 with P = 1 and q = D, with all three choices of class at o. Arc consistency plus DFS ran over states (P, class) with 192 values per vertex, 8 cores, about 2 min.
  - A complete board counts as a candidate only if (i) all three classes occur and (ii) it fails SH_grp^r for *every* absorbed class c ∈ {1, V_a, V_b}. Groups merge when a pair support is monomial, and the refined groups above are used.
- *Results.*
  - *First pass,* with unnormalised groups (a coarser, still sufficient test): 144 candidates, 0 unresolved. Realising them by solving for parameters with exactly pattern S_ab and all coefficients nonzero (tclose3_cand.py) shows the following. 48 are not realisable, which reflects the over-approximation for K = K′. The other 96 are admissible (Pauli residual ≤ 5·10⁻³⁰), inside the PF hull (facet ≤ 3.6·10⁻¹⁵), and pass the numerical SH_grp^r.
  - *Re-check* of the 144 with the refined groups: **0 candidates, 0 unresolved.** The refined test is stricter, so a job that was not a candidate in the first pass cannot become one. Hence no counterexample exists in this class. ∎

*Controls.*
- With the failure test loosened to "any cross pair, all three classes present", the solver finds boards for 1 of 40 sampled jobs. In the first pass it found 144, so the search is not vacuous.
- The two known three-class tuned boards (H.17.12d) do not contain the identity class, so they lie outside this theorem. They pass SH_grp^r numerically.

*Scope and what remains [OPEN].* Proved so far:
- every generic board (H.17.9);
- every two-class board (H.17.13);
- every three-class board containing the identity class (H.17.14).

Still open are boards with three classes none of which is the identity, and boards with ≥4 classes, in each case with at least one tuned pair. For three classes with a tuned pair there are about 145,000 tuned ordered pairs × 1,072 third classes, roughly 1.5·10⁸ triples before symmetry. A symmetry reduction under qubit permutations and cube relabelling would be needed. The pair-support consistency G_ab G_bc = G_ac is automatic in the per-class-pair model used here: each support is fixed once per class pair. Triple consistency is not imposed, which only enlarges the search and so is sound.

**H.17.15 Three non-identity classes: symmetry reduction and closure search (Oct 23 2026) [PROVED for the completed orbits listed below, by exhaustive exact enumeration with over-approximating supports; the remaining orbits are OPEN, and the run is resumable] (t3sym.py, tclose3g.py, tclose3g.log, tclose3g_done.txt.gz checkpoint, tclose3g_unres.py, tclose3g_ctrl.py/.log).**

*Symmetry group [PROVED].* Let G₄₈ = S₃ × (ℤ₂)³. It acts by permuting the three qubits, applied to Pauli strings and cube labels together, and by conjugating with a diagonal S gate on any subset m of the qubits. On strings the S part acts as z ↦ z ⊕ (x ∧ m).
- Qubit permutations relabel the parties, so they preserve admissibility, the Pauli rule H.8.1 and the PF hull.
- For the S part, write U_o = P_o V_k ↦ S P_o V_k S†. The left S is diagonal, so it does not change p(i|o). The right S† is absorbed into the source state.
- The S part preserves X-parts and x∨z, so it preserves the forbidden-string rule ((x|z)&D)==D. It also preserves which pair supports are nontrivial, so it preserves SH_grp^r and the groups H of H.17.11a/H.17.14.
- Hence a board is a counterexample if and only if its image is.
- Output flips, cube translations and a global left Pauli are already quotiented out by the WLOG root (o = 0, P = 1) and the translation normalisation. G ↔ G† maps a support to the same support (supp V† = supp V up to the Pauli map), so it gives no further reduction.
- Under G₄₈ the 1,071 non-identity classes fall into 61 orbits: 9 orbits of 2-term classes and 52 of 3-term classes.

*Reduction.* A board with exactly three non-identity classes and a tuned pair can be relabelled so that (a,b) is tuned. Then apply g ∈ G₄₈ so that a is an orbit representative. Here b runs over every class tuned with a, and c runs over every non-identity class.
- Boards using fewer classes are covered by H.17.13. Boards containing the identity class are covered by H.17.14. Boards with no tuned pair are generic and covered by H.17.9.
- Pair supports (S_ab, S_ac, S_bc) are taken from the H.17.12 lists, using "any nonempty subset of K" when K = K′, which is sound.
- Jobs equal up to the class-wise translations (S_ab, S_ac, S_bc) ↦ (S_ab+t_b, S_ac+t_c, S_bc+t_b+t_c) are solved once. This gives 17,855 jobs per 2-term orbit and 105,747 for each 3-term orbit completed so far, about 5.7·10⁶ jobs in all if that count holds for every orbit. Before the reduction there were 5.3·10⁷ pattern products for the representatives alone, and about 1.5·10⁸ class triples.

*Search.* The search is the same arc consistency plus DFS as in H.17.14, with 192 values (P, class) per vertex.
- At the root, the absorbed class a must fail SH_grp^r at a pair at o = 0, with each of the three classes allowed at o.
- A leaf counts as a candidate only if all three classes occur and SH_grp^r fails for every absorbed class. The test uses the Pauli-factored groups of H.17.14, and groups merge when a pair support is monomial.
- Each job has a node budget of 2·10⁵. Jobs that exhaust it are re-run with budget 2·10⁷ (tclose3g_unres.py).

*Results.* The run (8 cores; stopped at the round time limit on an orbit boundary) completed orbits 0–17, that is 18 of the 61 orbits (9 2-term and 9 3-term representatives a). These comprised 1,112,418 jobs. The search returned 27 candidates and 224 jobs that exhausted the budget (UNRESOLVED). The 8 UNRESOLVED jobs of orbit 0 were re-run with budget 2·10⁷ and all returned no counterexample. *Triple consistency [PROVED].* V_cV_a† = (V_cV_b†)(V_bV_a†), so S_ac ⊆ S_ab ⊕ S_bc (sumset), and likewise for the other two orderings. The condition is invariant under the job translations. Every one of the 27 candidates and every one of the 224 UNRESOLVED jobs violates it (tclose3g_cand.py), so none of them has a unitary realisation. For example, S_ab = {I} (the identity string) forces V_b ∝ V_a, and then S_bc must equal S_ac. **Hence no counterexample exists with the first tuned class in any of these 18 orbits [PROVED].** The remaining 43 3-term orbits are OPEN. At about 135 s per orbit they need roughly 97 min, resumable with `cd code/stochastic/cyclic/switchboard/h17; nohup python3 tclose3g.py >> tclose3g.log 2>&1 &` (finished orbits are skipped), followed by `python3 tclose3g_cand.py`. Imposing the consistency filter up front removes only about 4% of the jobs (101,637 of 105,747 for orbit 12), so it does not speed up the run.

*Controls.*
- *Loosened test.* With the failure test loosened to "any cross pair, all three classes present", the solver finds boards for 5 of 200 sampled orbit-0 jobs, so the search is not vacuous.
- *Known boards.* The two known three-class tuned boards (tb_25_3980, tb_26_554; H.17.12d) have pair supports ((0,4,32,36), (4,), (0,4,32,36)). For these supports the loosened solver finds a board, so the real board is representable. The real solver finds no counterexample (tclose3g_ctrl.log).

*Structural reduction [attempted; not achieved].* We tried to absorb one class of a ≥3-class board via H.17.11a so that the identity case H.17.14 would apply. This does not reduce the problem. After right-absorbing V_c, the new unitaries U_oV_c† are again ≤3-term only when the ratio supports stay small. In the K = K′ case, V_aV_c† can have 3 or 4 terms. Likewise "classes sharing one group H merge" is false in general. Two classes with the same H but a 3-term K = K′ ratio do not become one class, and their joint coset condition is exactly what the search checks. So the three-class case is handled only by enumeration.

*≥4 classes [OPEN].* The per-class-pair model extends verbatim, with (k choose 2) fixed pair supports and the same root and leaf tests. A cube has 8 vertices, so k ≤ 8. However, the number of jobs grows by a factor of about 10³–10⁵ per extra class. No reduction of the ≥4-class case to the ≤3-class case is known. A ≥4-class counterexample would have to fail SH_grp^r for every absorbed class. Its restriction to the vertices carrying three classes is not itself a board, so H.17.15 does not apply to it.

**H.17.7 Status after this round.**
- PROVED: the sign-variant lemma H.17.3, with the stated scope; the Pauli coset-transport theorem and the reduction SH_grp ⇒ PF blend (H.17.8a–b); in the generic-support model, every admissible ≤3-term board, non-X boards included, satisfies SH_grp and is therefore a PF blend for every source state (H.17.9, exhaustive exact enumeration).
- PROVED: every admissible three-class board {1, V_a, V_b}, tuned or generic, is a PF blend (H.17.14).
- PROVED: every admissible two-class ≤3-term board, tuned or generic, is a PF blend (H.17.13, exhaustive exact enumeration over 59,836 supports).
- PROVED (partial): boards with three non-identity classes whose first tuned class lies in one of the 18 completed G₄₈ orbits are PF blends (H.17.15). The other 43 orbits are OPEN, and the run is resumable.
- PROVED: complete classification of the cancellation patterns of V′V† for all pairs of ≤3-term classes. There is no cancellation unless the Klein groups meet. When they meet in two elements, at most one collided string vanishes. When K = K′, only the supports of H.17.12(b) occur.
- PROVED: right-absorbed coset transport, SH_grp^r ⇒ PF blend (H.17.11a). Each of the 19 regenerated tuned boards passes it, so each is a PF blend (supports read numerically, H.17.11b).
- PROVED (exact dual certificate): orbit 92 is the positivity orbit and holds on all of Valid (H.17.5).
- EXACT-CERTIFIED: the other 22 never-crossed orbits are not implied by validity alone (H.17.5).
- NUMERICAL:
  - pure non-X ≤3-term boards exist and all tested ones lie in the PF hull;
  - every hard board found satisfies SH⁺⁺;
  - the 19 tuned boards have explicit LP PF-blend decompositions at 4 source states each (H.17.11b);
  - no Z₁₆, continuous-phase or locally rotated X-type board violates any of the 22 genuine orbits.
- OPEN:
  - "non-X ≤3-term ⇒ PF blend" for tuned (non-generic) parameters. SH_grp fails on tuned boards (H.17.10), but the right-absorbed version SH_grp^r (H.17.11, proved sufficient) holds on all 19 regenerated tuned boards. That it holds on every admissible tuned board is open. It now holds on all 51 tuned boards (H.17.12d), and the cancellation patterns of V′V† are completely classified [proved] (H.17.12a–c); the closure is now **proved for every two-class board** (H.17.13) and every three-class board containing the identity class (H.17.14). Three non-identity classes are now reduced by G₄₈ to 61 orbits, of which 18 are proved (H.17.15). Remaining: the other 43 orbits and ≥4 classes, each with a tuned class pair;
  - the 22 genuine never-crossed orbits on general purifiable processes.

Runs were cut off at the time limit: nsearch2 seeds 13 and 14 ran with `timeout 840`, and their logs are the last checkpoints.

## Appendix I. Robustness: approximately blended versus approximately liftable (Oct 22 2026)

Norm: for classical processes, ||p - q||_1 = sum over (i,o) of |p(i|o) - q(i|o)|. For machines, the switchboard residual is rho(U) := sqrt(R(U)), the l2 norm of the forbidden Pauli coefficients (H.8.1).

**I.1 Blend-close implies liftable-close [proved, trivial].** If ||p - q||_1 <= eps with q in conv(PF), then p is within eps of a purifiable process, namely q (C.1). So delta = eps, in any norm. This uses only conv(PF) ⊆ Purif.

**I.2 The converse is the conjecture [proved, trivial; the conjecture is false by H.12.1, so the converse fails].** "dist(p, Purif) <= delta implies dist(p, conv PF) <= eps(delta) with eps(delta) -> 0" for all p holds iff the closure of Purif equals conv(PF). If the conjecture holds, then eps = delta. If it fails at some p*, then eps(0) >= dist(p*, conv PF) > 0. So no quantitative converse can be proved without proving the conjecture. A non-trivial robustness statement must therefore compare *approximately pure machines* with the hull, as follows.

**I.3 Residual controls operator purity [proved].** In family C, with or without ancillas, every entry of M M^dag - 1 has modulus at most 2 sqrt(2) rho(U).
*Proof.* Write K = (allowed part) + sum over forbidden sigma of c_sigma sigma. The allowed part reproduces the exact row inner products (H.8.1, H.8.2). A forbidden X^delta Z^b contributes c_{delta,b} sum_e (+-1) prod_k N_k(e_k). By Cauchy-Schwarz on unit rows, sum_e |prod_k N_k(e_k)| <= prod_k sum_{e_k} |N_k(e_k)| <= 1. Only the 8 strings with a = delta contribute, so the deviation is at most sum_b |c_{delta,b}| <= sqrt(8) rho. ∎

**I.4 Facet violation versus residual [numerical].** Facet violations bound distance: for a facet with +-1 coefficients and bound 0, f.p <= ||p - q||_1 for every q in the hull, so a violation v gives dist_1(p, conv PF) >= v. push.py minimises R subject to lambda_max(F_m(U)) >= v for facet-82 members (the best source state phi for each machine), in float64 with L-BFGS and an increasing penalty. Starts were random, Lugano, and the H.7 solutions rand_1, rand_15 and lug_21. There were 108 runs (curve.jsonl, curve2.jsonl).

| target v | runs | min R found | min R / v^2 | median R / v^2 |
|---|---|---|---|---|
| 0.01 | 21 | 3.27e-5 | 0.327 | 0.431 |
| 0.03 | 21 | 2.81e-4 | 0.312 | 0.387 |
| 0.1 | 21 | 3.19e-3 | 0.319 | 0.367 |
| 0.3 | 21 | 2.94e-2 | 0.326 | 0.370 |
| 0.5 | 8 | 9.27e-2 | 0.371 | 0.383 |
| 0.7 | 8 | 1.93e-1 | 0.394 | 0.419 |
| 0.9 | 8 | 3.52e-1 | 0.434 | 0.453 |

**Numerical statement (WITHDRAWN after H.12; the exact counterexample has R = 0 with positive violation).** For every switchboard machine found by push.py, facet-82 violation <= 1.79 rho(U), i.e. R >= 0.31 v^2. The ratio R/v^2 is nearly flat for small v, so near the hull boundary the violation grows at most linearly in rho: the modulus looks Lipschitz, not Hölder-1/2. The floor rises slowly for large v. These are local optima: the true infimum of R/v^2 could be lower, and only facet 82 was tested. For contrast, the H.7 sampled-unitary runs reached violations near 0.9 at sampled residual 0.03-0.05. That residual is a sampled average of ||M M^dag - 1||^2 and is not comparable with R. In the exact residual the trade-off is quadratic in v, so a violation is not cheap.

**I.5 Converse direction, numerically [numerical; WITHDRAWN after H.12].** Read the other way: a switchboard machine with rho(U) <= delta has statistics, at every source state, that violate facet 82 by at most about 1.79 delta. A machine whose statistics violate it by v is at least rho >= 0.56 v from pure. So in family C, numerically and for facet 82, "delta-close to liftable" (in the machine residual rho) implies "eps-close to the hull's facet-82 side" with eps ~ 1.8 delta. A full hull-distance version, over all 93 facet orbits, was not run.

## Appendix J. Facet-orbit tables for H.13-H.14 (Oct 23 2026)

Generated by code/stochastic/cyclic/switchboard/h13/tables.py from the committed data: facets from physics/facets/pf.out.gz, orbit labels and Z_4 maxima from xviol.npz, Z_8 maxima from xviol_z8.npz, exact Z_4 maxima from exactmax_part1/2.log, and Z_8 certificates from cert_z8.log. Strings are written i_A i_B i_C. "p(i|o)" is the probability of input string i given output string o.

*Representatives.* Each orbit's representative is its lowest-index facet. The integer form shown is the one with minimal ℓ¹ norm among the affine representatives that agree with the facet on all 744 process functions (found by LP, then scaled to integers and checked exactly). The representatives are exact. Other members of the orbit follow by the 384 symmetries (relabelling parties and local relabelling of inputs and outputs).

*Maxima.* "Rel." means the largest violation found divided by the facet's range on process functions. The Z_4 exact column gives the minimal polynomial of λ_min, the least eigenvalue of the facet operator Σ g P_{o,i} + g0 in the facet's normalisation. The violation is its root at the float-selected maximising board; this exact value is [proved, exact] for that board, while the claim that it is the maximum over the class is [numerical]. The Z_8 column is [numerical].

### J.1 The 22 genuine never-crossed orbits, plus orbit 92 (positivity) [numerical; orbit 92 proved in H.17.5]

Status for all 23 listed orbits (22 genuine, plus orbit 92 = positivity): never violated by the Z_4 (386 classes) and Z_8 (10,603 classes) X-type boards, maximised over source states [numerical].

*Update (H.17, Oct 23 2026).* None of the 23 orbits is violated by Z_16 X-type boards, continuous X-type phases, locally rotated (local Clifford and SU(2)^3) X-type boards, or pure non-X boards with ≤3 terms per outcome [numerical]. Orbits 4–11, 14, 25, 26, 28, 30, 31, 53, 54, 57, 66, 69, 75, 79 and 81 are violated at exact rational points of the valid polytope, so validity alone does not imply them [exact-certified, H.17.5]. Orbit 92 is the positivity orbit p(i|o) ≥ 0. On Valid its functional equals p(111|000) exactly, so it holds for every process [proved, H.17.5]. Only the other 22 orbits are genuinely open.

| orbit | size | representative facet (index) : integer inequality, value >= 0 on every PF |
|---|---|---|
| 4 | 384 | (72) - p(000|111) + p(011|010) - p(011|011) - p(011|100) + p(101|001) - p(101|011) - p(101|101) - p(110|100) + p(110|110) - p(110|111) + 2 >= 0 |
| 5 | 384 | (73) - p(000|111) + p(011|010) - p(011|011) - p(011|100) - p(101|001) + p(101|101) - p(101|111) - p(110|000) + p(110|010) - p(110|011) + 2 >= 0 |
| 6 | 384 | (76) - p(000|111) + p(011|000) - p(011|001) - p(011|100) + p(101|001) - p(101|011) - p(101|101) - p(110|000) + p(110|010) - p(110|111) + 2 >= 0 |
| 7 | 384 | (77) - p(000|111) + p(011|000) - p(011|001) - p(011|100) + p(101|000) - p(101|011) - p(101|100) - p(110|100) + p(110|110) - p(110|111) + 2 >= 0 |
| 8 | 384 | (78) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|000) + p(101|100) - p(101|111) - p(110|000) + p(110|010) - p(110|011) + 2 >= 0 |
| 9 | 384 | (79) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|001) + p(101|101) - p(101|111) - p(110|011) - p(110|100) + p(110|110) + 2 >= 0 |
| 10 | 384 | (86) - p(000|000) + p(000|001) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|011) - p(110|010) - p(110|100) + p(110|110) + 2 >= 0 |
| 11 | 384 | (94) - p(000|111) + p(011|010) - p(011|011) - p(011|110) + p(101|001) - p(101|011) - p(101|101) + p(110|000) - p(110|010) - p(110|101) + 2 >= 0 |
| 14 | 192 | (171) - p(001|011) - p(001|100) - p(010|110) + p(010|111) - p(011|100) - p(100|110) + p(100|111) - p(101|000) + p(101|001) - p(101|011) - p(110|010) - p(110|100) + 2 >= 0 |
| 25 | 192 | (191) - p(001|011) - p(001|100) - p(010|100) + p(010|101) + p(011|010) - p(011|011) - p(011|110) - p(100|010) + p(100|011) - p(101|111) - p(110|010) - p(110|100) + 2 >= 0 |
| 26 | 192 | (240) - p(000|000) - p(001|001) + p(010|101) + p(100|011) + p(110|001) - p(110|010) - p(110|100) + p(110|110) + p(111|000) + 1 >= 0 |
| 28 | 192 | (242) - p(000|000) - p(001|000) + p(010|101) + p(100|011) + p(110|001) - p(110|010) - p(110|100) + p(110|110) + p(111|001) + 1 >= 0 |
| 30 | 192 | (245) - p(000|000) - p(001|001) + p(010|111) + p(100|111) + p(110|000) - p(110|010) - p(110|100) + p(110|111) + p(111|110) + 1 >= 0 |
| 31 | 192 | (247) - p(000|000) - p(000|111) - p(001|000) - p(001|111) - p(011|111) - p(101|111) + p(110|000) - p(110|010) - p(110|100) + 2 >= 0 |
| 53 | 64 | (513) p(001|111) + p(010|111) - p(011|011) - p(011|101) - p(011|110) + 2p(011|111) - p(100|000) + p(111|111) + 1 >= 0 |
| 54 | 96 | (514) p(001|110) + p(010|100) - p(010|110) + p(010|111) + p(011|000) - p(011|001) - p(100|000) + p(100|001) + p(100|010) + p(101|110) - p(101|111) + p(111|000) + 1 >= 0 |
| 57 | 192 | (521) - p(000|110) - p(001|010) + p(001|011) - p(010|110) + p(010|111) - p(011|100) - p(100|100) + p(100|101) - p(101|110) - p(110|100) - p(111|000) + p(111|001) + 2 >= 0 |
| 66 | 96 | (561) - p(000|010) - p(001|010) + p(001|110) - p(010|001) + p(010|101) - p(011|001) + p(100|000) - p(100|100) - p(101|111) - p(110|100) + p(111|011) - p(111|111) + 2 >= 0 |
| 69 | 192 | (571) p(001|100) - p(001|101) + p(001|111) + p(010|111) - p(011|000) + p(011|010) - p(100|100) + p(100|101) + p(100|110) - p(110|001) + p(110|011) + p(111|110) + 1 >= 0 |
| 75 | 96 | (595) - p(000|110) - p(010|100) + p(010|101) + p(011|010) - p(011|011) - p(011|110) - p(100|100) + p(100|101) + p(101|010) - p(101|011) - p(101|110) - p(110|110) + 2 >= 0 |
| 79 | 64 | (698) p(001|010) - p(001|011) + p(001|111) + p(010|111) - p(011|001) - p(100|100) - p(110|001) + p(110|011) + p(111|010) + 1 >= 0 |
| 81 | 96 | (706) - p(000|101) - p(001|100) + p(001|110) - p(011|001) + p(011|011) - p(011|111) - p(100|100) + p(100|110) - p(101|101) - p(110|001) + p(110|011) - p(110|111) + 2 >= 0 |
| 92 | 64 | (6928) p(111|000) >= 0 |

### J.2 The 8 orbits first crossed at Z_8, exact certificates [proved, exact in Q(ζ8)]

Board class 10515 (ζ_8 phases listed in cert_z8.log) satisfies the Pauli rule exactly. With a rational source vector v it gives the following exact values of |v|²·(g·p+g0):

- orbit 16 facet 12406 : |v|^2 * (g.p+g0) = 491357689/800000000 + -702031757/1600000000 sqrt2 sign -1  value -0.006317 (relative -0.002106)
- orbit 19 facet 26054 : |v|^2 * (g.p+g0) = 234647147/400000000 + -670070737/1600000000 sqrt2 sign -1  value -0.005646 (relative -0.001882)
- orbit 21 facet 4386 : |v|^2 * (g.p+g0) = 29013371/50000000 + -82955477/200000000 sqrt2 sign -1  value -0.006317 (relative -0.002106)
- orbit 24 facet 8095 : |v|^2 * (g.p+g0) = 658166309/800000000 + -935696139/1600000000 sqrt2 sign -1  value -0.004338 (relative -0.001446)
- orbit 27 facet 15356 : |v|^2 * (g.p+g0) = 41033639/80000000 + -581201931/1600000000 sqrt2 sign -1  value -0.000794 (relative -0.000265)
- orbit 29 facet 7052 : |v|^2 * (g.p+g0) = 205385451/400000000 + -116351057/320000000 sqrt2 sign -1  value -0.000740 (relative -0.000247)
- orbit 52 facet 4396 : |v|^2 * (g.p+g0) = 509711951/800000000 + -144553793/320000000 sqrt2 sign -1  value -0.001703 (relative -0.000568)
- orbit 67 facet 12438 : |v|^2 * (g.p+g0) = 67432867/100000000 + -191210757/400000000 sqrt2 sign -1  value -0.001703 (relative -0.000568)

### J.3 Per-orbit maxima (all 93 orbits)

| orbit | Z4 exact max: min-eigenvalue polynomial, root (facet range r) | rel. Z4 | rel. Z8 (numerical) | status |
|---|---|---|---|---|
| 0 | 8x^4 - 44x^3 + 60x^2 - 20x - 3 root -0.110409076756 (r=5) | 0.02208 | 0.02208 | violated, Z4 |
| 1 | 8x^4 - 44x^3 + 60x^2 - 20x - 3 root -0.110409076756 (r=5) | 0.02208 | 0.02208 | violated, Z4 |
| 2 | 8x^4 - 44x^3 + 60x^2 - 20x - 3 root -0.110409076756 (r=5) | 0.02208 | 0.02208 | violated, Z4 |
| 3 | 8x^4 - 44x^3 + 60x^2 - 20x - 3 root -0.110409076756 (r=5) | 0.02208 | 0.02208 | violated, Z4 |
| 4 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 5 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 6 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 7 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 8 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 9 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 10 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 11 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 12 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 13 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 14 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 15 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 16 | - | 0 | 0.002106 | Z8 exact certificate (Q(zeta8)) |
| 17 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 18 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 19 | - | 0 | 0.001882 | Z8 exact certificate (Q(zeta8)) |
| 20 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 21 | - | 0 | 0.002106 | Z8 exact certificate (Q(zeta8)) |
| 22 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 23 | 32x^7 - 272x^6 + 904x^5 - 1484x^4 + 1240x^3 - 472x^2 + 46x + 7 root -0.0772693314944 (r=3) | 0.02576 | 0.02576 | violated, Z4 |
| 24 | - | 0 | 0.001446 | Z8 exact certificate (Q(zeta8)) |
| 25 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 26 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 27 | - | 0 | 0.0002648 | Z8 exact certificate (Q(zeta8)) |
| 28 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 29 | - | 0 | 0.0002468 | Z8 exact certificate (Q(zeta8)) |
| 30 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 31 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 32 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.02951 | violated, Z4 |
| 33 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.02951 | violated, Z4 |
| 34 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.03115 | violated, Z4 |
| 35 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.03115 | violated, Z4 |
| 36 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0462 | violated, Z4 |
| 37 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0495 | violated, Z4 |
| 38 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0495 | violated, Z4 |
| 39 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0462 | violated, Z4 |
| 40 | 8x^4 - 28x^3 + 24x^2 - 1 root -0.184324685944 (r=2) | 0.09216 | 0.09216 | violated, Z4 |
| 41 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0462 | violated, Z4 |
| 42 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.04659 | violated, Z4 |
| 43 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.0462 | violated, Z4 |
| 44 | 64x^7 - 384x^6 + 864x^5 - 896x^4 + 408x^3 - 48x^2 - 10x + 1 root -0.138600049779 (r=3) | 0.0462 | 0.04659 | violated, Z4 |
| 45 | 8x^4 - 28x^3 + 24x^2 - 1 root -0.184324685944 (r=2) | 0.09216 | 0.09216 | violated, Z4 |
| 46 | 8x^4 - 28x^3 + 24x^2 - 1 root -0.184324685944 (r=2) | 0.09216 | 0.09216 | violated, Z4 |
| 47 | 8x^4 - 28x^3 + 24x^2 - 1 root -0.184324685944 (r=2) | 0.09216 | 0.09216 | violated, Z4 |
| 48 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.02951 | violated, Z4 |
| 49 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.03124 | violated, Z4 |
| 50 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 51 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 52 | - | 0 | 0.0005678 | Z8 exact certificate (Q(zeta8)) |
| 53 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 54 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 55 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 56 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 57 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 58 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 59 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 60 | 2x^2 - 3x - 1 root -0.280776406404 (r=3) | 0.09359 | 0.09359 | violated, Z4 |
| 61 | 2x^2 - 3x - 1 root -0.280776406404 (r=3) | 0.09359 | 0.09359 | violated, Z4 |
| 62 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 63 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 64 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 65 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 66 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 67 | - | 0 | 0.0005678 | Z8 exact certificate (Q(zeta8)) |
| 68 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 69 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 70 | 4x^2 - 8x - 1 root -0.118033988750 (r=4) | 0.02951 | 0.02951 | violated, Z4 |
| 71 | 4096x^8 - 40960x^7 + 168960x^6 - 369664x^5 + 456704x^4 - 308544x^3 + 94288x^2 - 1088x - 3789 root -0.153450660324 (r=4) | 0.03836 | 0.03888 | violated, Z4 |
| 72 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 73 | 8x^4 - 44x^3 + 74x^2 - 33x - 7 root -0.153963018994 (r=3) | 0.05132 | 0.05132 | violated, Z4 |
| 74 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 75 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 76 | 2x^2 - 3x - 1 root -0.280776406404 (r=3) | 0.09359 | 0.09359 | violated, Z4 |
| 77 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 78 | 2x^2 - 3x - 1 root -0.280776406404 (r=3) | 0.09359 | 0.09359 | violated, Z4 |
| 79 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 80 | 16x^5 - 96x^4 + 192x^3 - 140x^2 + 23x + 3 root -0.0832404606833 (r=3) | 0.02775 | 0.02775 | violated, Z4 |
| 81 | - | 0 | 0 | never violated by Z4/Z8 X-type boards [numerical] |
| 82 | 4x^2 - 4x - 1 root -0.207106781187 (r=2) | 0.1036 | 0.1036 | violated, Z4 |
| 83 | 4x^2 - 4x - 1 root -0.207106781187 (r=2) | 0.1036 | 0.1036 | violated, Z4 |
| 84 | 4x^2 - 4x - 1 root -0.207106781187 (r=2) | 0.1036 | 0.1036 | violated, Z4 |
| 85 | 16x^5 - 72x^4 + 108x^3 - 60x^2 + 8x + 1 root -0.0757690071115 (r=2) | 0.03788 | 0.03788 | violated, Z4 |
| 86 | 256x^7 - 1536x^6 + 3456x^5 - 3584x^4 + 1664x^3 - 244x^2 - 17x + 3 root -0.102016817295 (r=2) | 0.05101 | 0.05101 | violated, Z4 |
| 87 | 32x^6 - 176x^5 + 352x^4 - 304x^3 + 98x^2 - x - 2 root -0.116604771529 (r=2) | 0.0583 | 0.0583 | violated, Z4 |
| 88 | 256x^7 - 1536x^6 + 3456x^5 - 3584x^4 + 1664x^3 - 244x^2 - 17x + 3 root -0.102016817295 (r=2) | 0.05101 | 0.05101 | violated, Z4 |
| 89 | 32x^6 - 176x^5 + 352x^4 - 304x^3 + 98x^2 - x - 2 root -0.116604771529 (r=2) | 0.0583 | 0.0583 | violated, Z4 |
| 90 | 16x^5 - 72x^4 + 108x^3 - 60x^2 + 8x + 1 root -0.0757690071115 (r=2) | 0.03788 | 0.03788 | violated, Z4 |
| 91 | 2x^2 - 3x - 1 root -0.280776406404 (r=2) | 0.1404 | 0.1404 | violated, Z4 |
| 92 | - | 0 | 0 | positivity facet p(i|o) >= 0: holds for every process [proved, H.17.5] |

### J.4 Integer representatives of all 93 orbits

| orbit | size | representative facet (index) : integer inequality, value >= 0 on every PF |
|---|---|---|
| 0 | 384 | (0) p(001|111) + p(010|111) + p(011|000) + p(011|001) + p(011|010) - 2p(011|011) - p(011|100) + p(011|111) - p(100|100) + p(101|001) - p(101|101) + p(111|010) + p(111|011) + p(111|101) + 1 >= 0 |
| 1 | 384 | (2) p(001|111) + p(010|101) - p(011|001) + 2p(011|010) + p(011|101) - p(011|110) - p(100|100) + p(101|001) - p(101|101) + 2p(111|001) + p(111|010) - p(111|011) + p(111|111) + 1 >= 0 |
| 2 | 384 | (3) p(001|111) + p(010|101) - p(011|001) + 2p(011|010) + p(011|101) - p(011|110) - p(100|100) + p(110|000) - p(110|100) - p(111|000) + 2p(111|001) + p(111|010) + p(111|100) + 1 >= 0 |
| 3 | 384 | (6) p(001|010) - p(001|011) + p(001|111) + p(010|101) - p(011|000) + p(011|010) + p(011|011) + p(011|101) - p(011|111) - p(100|100) + p(110|000) - p(110|100) + p(111|000) + p(111|010) + p(111|101) + 1 >= 0 |
| 4 | 384 | (72) - p(000|111) + p(011|010) - p(011|011) - p(011|100) + p(101|001) - p(101|011) - p(101|101) - p(110|100) + p(110|110) - p(110|111) + 2 >= 0 |
| 5 | 384 | (73) - p(000|111) + p(011|010) - p(011|011) - p(011|100) - p(101|001) + p(101|101) - p(101|111) - p(110|000) + p(110|010) - p(110|011) + 2 >= 0 |
| 6 | 384 | (76) - p(000|111) + p(011|000) - p(011|001) - p(011|100) + p(101|001) - p(101|011) - p(101|101) - p(110|000) + p(110|010) - p(110|111) + 2 >= 0 |
| 7 | 384 | (77) - p(000|111) + p(011|000) - p(011|001) - p(011|100) + p(101|000) - p(101|011) - p(101|100) - p(110|100) + p(110|110) - p(110|111) + 2 >= 0 |
| 8 | 384 | (78) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|000) + p(101|100) - p(101|111) - p(110|000) + p(110|010) - p(110|011) + 2 >= 0 |
| 9 | 384 | (79) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|001) + p(101|101) - p(101|111) - p(110|011) - p(110|100) + p(110|110) + 2 >= 0 |
| 10 | 384 | (86) - p(000|000) + p(000|001) - p(000|111) + p(011|000) - p(011|001) - p(011|100) - p(101|011) - p(110|010) - p(110|100) + p(110|110) + 2 >= 0 |
| 11 | 384 | (94) - p(000|111) + p(011|010) - p(011|011) - p(011|110) + p(101|001) - p(101|011) - p(101|101) + p(110|000) - p(110|010) - p(110|101) + 2 >= 0 |
| 12 | 384 | (168) - p(001|011) - p(001|100) - p(010|110) + p(010|111) - p(011|011) - p(011|100) - p(100|110) + p(100|111) - p(101|000) + p(101|001) - p(101|011) - p(110|010) + 2 >= 0 |
| 13 | 384 | (169) p(001|000) - p(001|001) - p(001|010) - p(001|100) - p(010|110) + p(010|111) - p(011|011) - p(011|100) - p(100|010) + p(100|011) - p(101|110) - p(110|110) + 2 >= 0 |
| 14 | 192 | (171) - p(001|011) - p(001|100) - p(010|110) + p(010|111) - p(011|100) - p(100|110) + p(100|111) - p(101|000) + p(101|001) - p(101|011) - p(110|010) - p(110|100) + 2 >= 0 |
| 15 | 384 | (172) p(000|100) - p(001|011) + p(010|100) - p(010|110) + p(010|111) + p(100|000) - p(100|010) + p(100|011) - p(101|111) + p(111|001) + p(111|100) - p(111|101) + 1 >= 0 |
| 16 | 384 | (173) p(001|000) - p(001|001) - p(001|010) - p(001|100) - p(010|110) + p(010|111) - p(011|100) - p(100|010) + p(100|011) - p(101|110) - p(110|000) - p(110|110) + 2 >= 0 |
| 17 | 384 | (174) - p(001|011) - p(001|100) - p(010|110) + p(010|111) - p(011|011) - p(011|101) - p(011|110) + p(011|111) - p(100|110) + p(100|111) - p(101|011) - p(110|010) + 2 >= 0 |
| 18 | 384 | (175) - p(001|011) - p(001|100) - p(010|110) + p(010|111) - p(011|011) - p(011|101) - p(011|110) + p(011|111) - p(100|010) + p(100|011) - p(101|111) - p(110|110) + 2 >= 0 |
| 19 | 192 | (177) - p(000|000) + p(000|010) + p(000|100) - p(001|000) + p(010|100) - p(010|110) + p(010|111) + p(100|011) + p(110|001) - p(110|010) - p(110|101) + p(111|001) + 1 >= 0 |
| 20 | 384 | (178) - p(001|000) + p(001|001) - p(001|011) - p(001|101) - p(010|110) + p(010|111) - p(011|101) - p(100|010) + p(100|011) - p(101|000) - p(101|111) - p(110|000) + 2 >= 0 |
| 21 | 384 | (179) - p(000|000) + p(000|010) + p(000|100) - p(001|000) + p(010|111) - p(011|101) + p(011|111) - p(100|010) + p(100|011) + p(100|110) - p(110|000) + p(111|111) + 1 >= 0 |
| 22 | 384 | (181) - p(001|011) - p(001|100) - p(010|100) + p(010|101) - p(011|001) - p(011|100) + p(011|101) - p(011|111) - p(100|010) + p(100|011) - p(101|111) - p(110|100) + 2 >= 0 |
| 23 | 384 | (183) - p(001|010) - p(001|101) - p(010|100) + p(010|101) - p(011|001) - p(011|010) + p(011|011) - p(011|111) - p(100|010) + p(100|011) - p(101|110) - p(110|100) + 2 >= 0 |
| 24 | 192 | (187) - p(001|010) - p(001|101) - p(010|100) + p(010|101) - p(011|010) + p(011|011) - p(011|111) - p(100|010) + p(100|011) - p(101|110) - p(110|010) - p(110|100) + 2 >= 0 |
| 25 | 192 | (191) - p(001|011) - p(001|100) - p(010|100) + p(010|101) + p(011|010) - p(011|011) - p(011|110) - p(100|010) + p(100|011) - p(101|111) - p(110|010) - p(110|100) + 2 >= 0 |
| 26 | 192 | (240) - p(000|000) - p(001|001) + p(010|101) + p(100|011) + p(110|001) - p(110|010) - p(110|100) + p(110|110) + p(111|000) + 1 >= 0 |
| 27 | 384 | (241) - p(000|000) - p(001|001) + p(010|101) + p(100|111) - p(110|100) + p(110|101) + p(111|000) - p(111|010) + p(111|110) + 1 >= 0 |
| 28 | 192 | (242) - p(000|000) - p(001|000) + p(010|101) + p(100|011) + p(110|001) - p(110|010) - p(110|100) + p(110|110) + p(111|001) + 1 >= 0 |
| 29 | 384 | (243) - p(000|000) - p(001|000) + p(010|101) + p(100|111) - p(110|100) + p(110|101) + p(111|001) - p(111|011) + p(111|111) + 1 >= 0 |
| 30 | 192 | (245) - p(000|000) - p(001|001) + p(010|111) + p(100|111) + p(110|000) - p(110|010) - p(110|100) + p(110|111) + p(111|110) + 1 >= 0 |
| 31 | 192 | (247) - p(000|000) - p(000|111) - p(001|000) - p(001|111) - p(011|111) - p(101|111) + p(110|000) - p(110|010) - p(110|100) + 2 >= 0 |
| 32 | 384 | (261) - p(001|000) + p(001|001) + p(001|010) - p(010|110) - p(011|100) + p(011|101) - p(011|111) - p(100|001) + p(100|011) + p(100|101) + p(101|001) + p(111|101) + 1 >= 0 |
| 33 | 384 | (263) - p(001|000) + p(001|001) + p(001|010) - p(010|110) - p(011|100) + p(011|101) - p(011|111) + p(100|001) - p(100|101) + p(100|111) + p(101|101) + p(111|001) + 1 >= 0 |
| 34 | 384 | (265) - p(001|000) + p(001|001) + p(001|010) - p(010|100) - p(011|101) - p(011|110) + p(011|111) - p(100|001) + p(100|011) + p(100|101) + p(101|001) + p(111|111) + 1 >= 0 |
| 35 | 384 | (267) - p(001|000) + p(001|001) + p(001|010) - p(010|110) - p(011|110) + p(100|001) - p(100|101) + p(100|111) + p(101|101) + p(110|000) - p(110|010) + p(111|001) + 1 >= 0 |
| 36 | 384 | (280) - p(001|101) - p(010|110) - p(011|111) + p(100|010) - p(100|110) + p(100|111) + p(110|000) - p(110|010) + p(111|000) + 1 >= 0 |
| 37 | 384 | (281) - p(001|100) - p(010|110) - p(011|100) + p(011|101) - p(011|111) + p(100|010) - p(100|110) + p(100|111) + p(111|001) + 1 >= 0 |
| 38 | 384 | (282) - p(001|100) - p(010|100) - p(011|100) + p(100|011) + p(101|001) - p(101|100) + p(110|011) - p(110|111) + p(111|011) + 1 >= 0 |
| 39 | 384 | (283) - p(001|100) - p(010|100) - p(011|100) - p(100|001) + p(100|011) + p(100|101) - p(110|100) + p(110|110) + p(111|111) + 1 >= 0 |
| 40 | 384 | (288) - p(001|101) - p(010|110) + p(011|011) - p(011|111) + p(100|011) - p(101|101) + p(110|001) - p(110|101) + p(111|000) + 1 >= 0 |
| 41 | 384 | (292) p(000|100) + p(100|000) + p(100|011) + p(101|001) + p(110|011) + p(110|110) - p(110|111) + p(111|001) + p(111|010) >= 0 |
| 42 | 384 | (293) - p(001|100) - p(010|110) - p(011|110) + p(100|010) - p(100|110) + p(100|111) + p(110|000) - p(110|010) + p(111|001) + 1 >= 0 |
| 43 | 384 | (294) - p(001|100) - p(010|110) - p(011|110) + p(100|011) + p(101|001) - p(101|100) + p(110|001) - p(110|101) + p(111|001) + 1 >= 0 |
| 44 | 384 | (295) - p(001|100) - p(010|100) - p(011|101) - p(011|110) + p(011|111) - p(100|001) + p(100|011) + p(100|101) + p(111|111) + 1 >= 0 |
| 45 | 384 | (300) - p(000|000) + p(000|100) - p(001|000) - p(010|010) + p(100|011) - p(101|100) + p(110|001) - p(110|101) + p(111|001) + 1 >= 0 |
| 46 | 384 | (302) - p(000|000) + p(000|100) - p(001|000) - p(010|010) + p(100|011) - p(101|000) + p(101|011) - p(101|111) + p(111|001) + 1 >= 0 |
| 47 | 384 | (308) - p(000|000) + p(000|100) - p(001|000) - p(010|000) + p(100|011) - p(101|100) + p(110|011) - p(110|111) + p(111|011) + 1 >= 0 |
| 48 | 384 | (504) p(001|111) + p(010|111) - p(011|011) - p(011|100) + p(011|111) - p(100|100) - p(101|000) + p(101|001) + p(101|100) + p(111|011) + 1 >= 0 |
| 49 | 384 | (506) p(001|111) + p(010|111) - p(011|011) - p(011|100) + p(011|111) - p(100|000) + p(110|000) - p(110|100) + p(110|110) + p(111|111) + 1 >= 0 |
| 50 | 384 | (508) p(001|111) + p(010|100) - p(010|110) + p(010|111) + p(011|010) - p(011|011) - p(011|100) + p(011|101) - p(100|100) + p(111|001) + 1 >= 0 |
| 51 | 384 | (509) p(001|111) + p(010|111) + p(011|010) - p(011|011) - p(011|100) + p(011|111) - p(100|000) - p(110|100) + p(110|110) + p(111|111) + 1 >= 0 |
| 52 | 192 | (512) p(001|111) + p(010|111) - p(011|011) - p(011|100) + p(011|111) - p(100|100) - p(111|000) + p(111|001) + p(111|010) + 1 >= 0 |
| 53 | 64 | (513) p(001|111) + p(010|111) - p(011|011) - p(011|101) - p(011|110) + 2p(011|111) - p(100|000) + p(111|111) + 1 >= 0 |
| 54 | 96 | (514) p(001|110) + p(010|100) - p(010|110) + p(010|111) + p(011|000) - p(011|001) - p(100|000) + p(100|001) + p(100|010) + p(101|110) - p(101|111) + p(111|000) + 1 >= 0 |
| 55 | 384 | (516) p(001|110) + p(010|100) - p(010|110) + p(010|111) + p(011|000) - p(011|001) - p(100|100) + p(101|110) - p(101|111) + p(111|000) + 1 >= 0 |
| 56 | 384 | (519) - p(001|010) + p(001|011) + p(001|110) + p(010|100) - p(010|110) + p(010|111) - p(100|000) - p(111|000) + p(111|001) + p(111|100) + 1 >= 0 |
| 57 | 192 | (521) - p(000|110) - p(001|010) + p(001|011) - p(010|110) + p(010|111) - p(011|100) - p(100|100) + p(100|101) - p(101|110) - p(110|100) - p(111|000) + p(111|001) + 2 >= 0 |
| 58 | 384 | (532) p(001|111) + p(010|111) + p(011|000) - p(011|011) - p(011|100) + p(011|111) - p(100|100) + p(111|010) - p(111|110) + p(111|111) + 1 >= 0 |
| 59 | 384 | (534) p(001|111) + p(010|111) + p(011|000) - p(011|011) - p(011|100) + p(011|111) - p(100|000) - p(111|001) + p(111|011) + p(111|101) + 1 >= 0 |
| 60 | 384 | (543) p(001|100) - p(001|101) + p(001|111) + p(010|000) - p(010|001) + p(010|101) - p(100|101) + p(111|010) + p(111|100) - p(111|110) + 1 >= 0 |
| 61 | 384 | (545) p(001|100) - p(001|101) + p(001|111) + p(010|000) - p(010|001) + p(010|101) - p(100|001) + p(111|000) - p(111|010) + p(111|110) + 1 >= 0 |
| 62 | 384 | (548) p(001|111) + p(010|000) - p(010|001) + p(010|101) + p(011|010) - p(011|011) - p(011|100) + p(011|101) - p(100|101) + p(111|001) + 1 >= 0 |
| 63 | 384 | (550) p(001|111) + p(010|000) - p(010|001) + p(010|101) + p(011|010) - p(011|011) - p(011|100) + p(011|101) - p(100|001) + p(111|101) + 1 >= 0 |
| 64 | 384 | (555) p(001|111) + p(010|000) - p(010|001) + p(010|101) - p(011|110) + p(011|111) - p(100|001) - p(101|100) + p(101|101) + p(111|101) + 1 >= 0 |
| 65 | 384 | (558) - p(001|010) + p(001|011) + p(001|110) + p(010|000) - p(010|001) + p(010|101) - p(100|101) + p(111|011) + p(111|101) - p(111|111) + 1 >= 0 |
| 66 | 96 | (561) - p(000|010) - p(001|010) + p(001|110) - p(010|001) + p(010|101) - p(011|001) + p(100|000) - p(100|100) - p(101|111) - p(110|100) + p(111|011) - p(111|111) + 2 >= 0 |
| 67 | 192 | (562) p(001|111) + p(010|101) - p(011|001) - p(011|100) + 2p(011|101) - p(011|111) - p(100|100) + p(111|001) + 1 >= 0 |
| 68 | 384 | (569) p(001|100) - p(001|101) + p(001|111) + p(010|111) - p(011|000) + p(011|010) - p(100|000) - p(110|001) + p(110|011) + p(111|110) + 1 >= 0 |
| 69 | 192 | (571) p(001|100) - p(001|101) + p(001|111) + p(010|111) - p(011|000) + p(011|010) - p(100|100) + p(100|101) + p(100|110) - p(110|001) + p(110|011) + p(111|110) + 1 >= 0 |
| 70 | 384 | (572) p(001|111) + p(010|101) - p(011|001) + p(011|101) - p(011|110) - p(100|100) - p(101|000) + p(101|001) + p(101|100) + p(111|001) + 1 >= 0 |
| 71 | 384 | (573) p(001|111) + p(010|101) - p(011|001) + p(011|101) - p(011|110) - p(100|100) + p(110|000) - p(110|010) + p(110|110) + p(111|001) + 1 >= 0 |
| 72 | 384 | (577) p(001|111) + p(010|101) - p(011|001) + p(011|011) + p(011|101) - p(011|110) - p(100|000) - p(101|100) + p(101|101) + p(111|101) + 1 >= 0 |
| 73 | 384 | (583) p(001|111) + p(010|101) - p(011|001) + p(011|010) + p(011|101) - p(011|110) - p(100|000) - p(111|000) + p(111|001) + p(111|100) + 1 >= 0 |
| 74 | 384 | (593) p(001|110) - p(010|100) + p(010|101) + p(010|110) + p(011|010) - p(011|011) - p(100|000) + p(101|010) - p(101|011) + p(111|110) + 1 >= 0 |
| 75 | 96 | (595) - p(000|110) - p(010|100) + p(010|101) + p(011|010) - p(011|011) - p(011|110) - p(100|100) + p(100|101) + p(101|010) - p(101|011) - p(101|110) - p(110|110) + 2 >= 0 |
| 76 | 128 | (609) p(001|100) - p(001|101) + p(001|111) + p(010|010) - p(010|011) + p(010|111) - p(100|001) - p(111|000) + p(111|010) + p(111|100) + 1 >= 0 |
| 77 | 384 | (612) - p(001|010) + p(001|011) + p(001|110) + p(010|010) - p(010|011) + p(010|111) - p(100|101) + p(111|001) - p(111|101) + p(111|111) + 1 >= 0 |
| 78 | 128 | (673) - p(001|100) + p(001|101) + p(001|110) + p(010|000) - p(010|001) + p(010|101) - p(100|101) + p(111|011) + p(111|101) - p(111|111) + 1 >= 0 |
| 79 | 64 | (698) p(001|010) - p(001|011) + p(001|111) + p(010|111) - p(011|001) - p(100|100) - p(110|001) + p(110|011) + p(111|010) + 1 >= 0 |
| 80 | 384 | (705) - p(001|100) + p(001|101) + p(001|110) + p(010|111) - p(011|001) + p(011|011) - p(100|000) - p(110|001) + p(110|011) + p(111|111) + 1 >= 0 |
| 81 | 96 | (706) - p(000|101) - p(001|100) + p(001|110) - p(011|001) + p(011|011) - p(011|111) - p(100|100) + p(100|110) - p(101|101) - p(110|001) + p(110|011) - p(110|111) + 2 >= 0 |
| 82 | 384 | (1732) p(100|000) - p(100|100) + p(101|001) + p(110|000) + p(111|000) + p(111|011) >= 0 |
| 83 | 192 | (1739) p(001|000) - p(001|001) + p(011|010) + p(101|100) + p(111|010) + p(111|100) >= 0 |
| 84 | 192 | (1745) p(100|000) - p(100|100) + p(101|000) + p(110|000) + p(111|001) + p(111|010) >= 0 |
| 85 | 192 | (1926) p(001|010) - p(010|100) + p(011|010) - p(011|011) - p(011|100) - p(100|100) + p(111|010) + 1 >= 0 |
| 86 | 384 | (1927) p(001|010) - p(010|100) + p(011|010) - p(011|011) - p(011|100) - p(100|000) + p(111|110) + 1 >= 0 |
| 87 | 192 | (1929) p(001|010) - p(010|110) + p(011|000) - p(011|001) - p(011|110) - p(100|000) + p(111|100) + 1 >= 0 |
| 88 | 384 | (1960) - p(001|101) + p(010|011) - p(011|000) + p(011|010) - p(011|111) - p(100|100) + p(111|010) + 1 >= 0 |
| 89 | 192 | (1961) - p(001|101) + p(010|011) - p(011|000) + p(011|010) - p(011|111) - p(100|000) + p(111|110) + 1 >= 0 |
| 90 | 192 | (1962) - p(001|100) + p(010|011) - p(011|001) + p(011|011) - p(011|110) - p(100|100) + p(111|011) + 1 >= 0 |
| 91 | 96 | (5160) p(110|000) + p(110|111) + p(111|001) + p(111|100) - p(111|101) + p(111|111) >= 0 |
| 92 | 64 | (6928) p(111|000) >= 0 |

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
32. V. Vilasini and R. Renner, Embedding cyclic information-theoretic structures in acyclic spacetimes: no-go results for indefinite causality, Physical Review A 110, 022227 (2024); arXiv:2203.11245.
33. V. Vilasini and R. Colbeck, A general framework for cyclic and fine-tuned causal models and their compatibility with space-time, Physical Review A 106, 032204 (2022); arXiv:2109.12128.
34. V. Vilasini and R. Colbeck, Impossibility of superluminal signalling in Minkowski space-time does not rule out causal loops, Physical Review Letters 129, 110401 (2022); arXiv:2206.12887.
35. N. Paunković and M. Vojinović, Causal orders, quantum circuits and spacetime: distinguishing between definite and superposed causal orders, Quantum 4, 275 (2020); arXiv:1905.09682.
36. R. Kunjwal and O. Oreshkov, Nonclassicality in correlations without causal order, arXiv:2307.02565 (2023; v3 2025).
37. M. Araújo, P. A. Guérin and Ä. Baumeler, Quantum computation with indefinite causal structures, Physical Review A 96, 052315 (2017); arXiv:1706.09854.
