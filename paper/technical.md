# Technical section: every process function purifies to a unitary process

Draft. Not refereed. This is the proof section the long essay was missing, together with the novelty claim.

## Statement

Let each party have a finite alphabet carrying an abelian group law, written additively. Bits under XOR are the case that matters. A process function is a map w from output strings to input strings such that, for every tuple of local functions, the composition has exactly one fixed point.

Theorem. Every process function purifies to a unitary process. The dilation is the source-and-sink permutation unitary of Baumeler, Costa, Ralph, Wolf and Zych, Theorem 2:

U |o, e> = |w(o) + e, o>.

For any local unitaries, possibly acting on a local ancilla, the source-to-sink operator induced by U is unitary. Every tuple of local instruments therefore induces a completely positive trace-preserving map from source to sink. The Choi operator of U is a valid unitary process. Fixing the source at the identity element of the group recovers w.

## Lemma

If w is a process function and s is not equal to s', then some party k has s_k different from s'_k and w_k(s) equal to w_k(s').

Proof. Suppose not. Then agreement of the process outputs already forces agreement of the strings. Define a local function that sends w_k(s) to s_k and w_k(s') to s'_k, and extend it arbitrarily off those points. The two clauses agree wherever the inputs agree, so the local map is a function. Both strings are then fixed points of one intervention. A process function cannot have that.

The swap is the witness in the other direction. The strings (0,1) and (1,0), under the map that exchanges its arguments, are both fixed by negation on each side. The identity loop fails for the same reason. Both are already known not to be process functions. The lemma says why, in a form the contraction can use.

## Cancellation

U is a permutation unitary for any w, process function or not. Validity uses the lemma.

The source-to-sink matrix element, with a local unitary V_k at each party, is the product over parties of the amplitude for V_k to take the shifted source bit to the sink bit:

M_{s,e} = product_k <s_k| V_k |w_k(s) + e_k>.

Change variables by i_k = w_k(s) + e_k. The sum over the source factors across parties. The (s, s') entry of M M-dagger is a product, over k, of the overlap between row s_k of V_k and row s'_k shifted by delta_k = w_k(s') - w_k(s).

If s = s', every shift vanishes and each factor is a row norm, hence 1. If s is not s', the lemma supplies a party with shift zero and distinct row indices. That factor is the inner product of two distinct rows of a unitary, ancilla included, hence zero. So M M-dagger is the identity.

A local completely positive trace-preserving map is a unitary on a local ancilla followed by a partial trace. The partial trace of a unitary dilation is completely positive and trace-preserving. Fixing the source at the identity recovers w.

Unitarity of the local operators does not kill the shift by itself. The process-function clause does. That is why the swap and the identity loop fail the same contraction.

## What was kernel-checked

A Lean 4.34.1 file accepted the exclusivity lemma and the gram cancellation under a hypothesis of row orthonormality. The identification of that gram entry with the concrete contraction of U against complex local unitaries was not kernel-checked. Row orthogonality is the standard step. The step that could have failed is the combinatorial one, and it did not.

## Why this is novel

The 2019 paper proved the reversible extension and said the quantum step was open: it is unclear whether every classical deterministic process function lifts to a valid unitary quantum process. They checked one finite-dimensional case. Araujo, Feix, Navascues and Brukner gave a unitary extension of the Lugano function in 2017, reconstructed as a routed circuit by Vanrietvelde, Ormrod, Kristjansson and Barrett. Those are existence proofs for one function.

Daher Ahmed and Kunjwal, arXiv:2610.00579, 30 September 2026, conjectured that every process function purifies to a unitary process. They proved it under two sufficient conditions, mutual exclusivity of control conditions and unambiguity, and they noted that the bare permutation unitary of the reversible extension may fail to be a valid process. Neither sufficient condition is necessary. Lugano sits outside that subclass and was already known to work by another construction.

The argument here does not use those conditions. The dilation is the source-and-sink permutation unitary, and the process-function clause is the cancellation. If the lemma stands, the 2026 conjecture is a theorem, and the reason a process function lifts is the same reason it was consistent: the forbidden double fixed point is the forbidden off-diagonal. That identification is the novel step. The Lugano function is an instance, not the argument.

## What is not claimed

The result does not embed the process in a spacetime. The wormhole billiard has the wrong multiplicity. Post-selection realises the event list conditional on success; that is a simulation, not this dilation. Freedom is not settled. The Leifer-Pusey no-go is not answered. Purifiability of every extensibly causal process remains open; the theorem covers deterministic classical process functions only.
