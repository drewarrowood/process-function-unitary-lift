# Every process function lifts to a unitary process

**Draft note. Not submitted. Not refereed.** Canonical source of the paper; `lift.pdf` is built from this file.

## Abstract

A process function is a classical map w from the outputs of several parties to their inputs such that every choice of local deterministic interventions has exactly one fixed point. Baumeler, Costa, Ralph, Wolf and Zych showed that every process function extends to a bijection by adding a source and a sink, and left open whether every such bijection quantizes to a valid unitary quantum process; Daher Ahmed and Kunjwal (2026) state this as a conjecture and prove it for a subclass. We give a short argument that it holds for every process function with finite alphabets: the permutation unitary U|o,e> = |w(o)+e, o> composed with arbitrary local unitaries induces a unitary from source to sink. The key combinatorial fact, that two distinct output strings always disagree at some party whose input w assigns equally, is the pairwise-exclusivity property of Dourdent et al. (2026). The philosophical sections read the result as saying that fixed-point consistency is already a quantization condition. The result is a draft: the exclusivity lemma and the identity M M^dagger = 1 (complex amplitudes, any finite number of parties, any finite alphabets, local ancillas) are machine-checked in Lean 4 with Mathlib (theorems PFUL.induced_mul_conjTranspose, PFUL.induced_conjTranspose_mul and PFUL.induced_unitary, the last stating membership in the unitary group; standard axioms only). The step from "unitary under local unitaries" to "valid process" (Stinespring, Appendix A) is a standard paper argument and is not formalised.

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

General relativity makes the question physical. Gödel's 1949 solution has closed timelike curves. Morris, Thorne and Yurtsever showed that a traversable wormhole, if one could be held open, can be converted into a time machine by relative motion of the mouths. The Cauchy problem on the resulting spacetime is the grandfather paradox in differential equations. Friedman, Morris, Novikov, Thorne and collaborators proposed, in 1990, that only self-consistent solutions occur. Echeverria, Klinkhammer and Thorne then integrated the hard-sphere billiard on a wormhole and found initial data with one consistent continuation, data with two, and data for which none was apparent. Carlini, Frolov, Mensky, Novikov and Solodukhin derived a version of self-consistency from stationarity of the action in a model, and found the same underdetermination. Novikov's principle removes inconsistent solutions. It does not choose among consistent ones. Earman's survey of the classical problem remains the right warning: a consistency condition that is imposed after the dynamics is not a dynamics.

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

Freedom is not settled. Nothing here decides whether an agent whose output is an argument of an earlier input has a choice. The fixed-point clause says the choice, if made, completes uniquely. It does not say the choice was open. Whether this is an adequate reply to Black depends on whether consistency conditions may rule out interventions, or only rule out histories given the interventions. The note takes the first reading, and the formalism is built for it.

The combinatorial lemma is finite for any fixed alphabet and is the piece an attacker has to break. The linear algebra after it is row orthogonality. See lean/STATUS.md for exactly what is and is not machine-checked.


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
- For the other 49 orbits (dim V_W ≥ 82) the random-form isotropy test was inconclusive, and gradient searches did not finish within our compute budget. Their status is open.
- No purifiable non-mixture has been found. That is weak evidence, because the large cases are untested.
- All 1,488 mixtures (q + E_ex1)/2 and (q + 4 E_ex1)/5, with q one of the 744 process functions, lie outside the process-function hull (LP check). They are untested candidates for non-extreme counterexamples.

*Proof idea for "only if" (not completed).* A purification U restricted to classical permutation instruments gives a unitary M for every reversible local classical operation. One would like to show that M's action on basis states then decomposes into permutations, giving a deterministic decomposition. We have not proved this. E_ex1 shows the classical consistency of W alone is not enough.

**Answer.** Not every classical process admits a unitary extension: E_ex1 (and one other vertex orbit) provably does not. Mixtures of process functions do. Whether those are the only ones is the open conjecture above.

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
