# Every process function lifts to a unitary process

**Draft note, in the style of Foundations of Physics**

## Abstract

A process function is a classical map from the outputs of several parties to their inputs such that every choice of local deterministic interventions has exactly one fixed point. Such maps are the deterministic skeletons of logically consistent processes without a predefined causal order. Baumeler, Costa, Ralph, Wolf and Zych showed that every process function extends to a bijection by the addition of a source and a sink, and left open whether every such bijection quantizes to a valid unitary quantum process. Daher Ahmed and Kunjwal conjectured that it does. We give an argument that it does. The dilation is the permutation unitary of the source-and-sink extension. For any tuple of local unitaries, the induced source-to-sink operator is unitary, because a process function cannot have two distinct global strings that agree on the output of the process wherever they disagree as strings. Local instruments then induce a completely positive trace-preserving map by the usual dilation. Fixing the source at the identity recovers the original process function.

## 1. Why this is worth settling

Two programmes meet here, and both are blocked on the same implication.

The first is the classical theory of causal loops. A deterministic process with no predefined order is logically consistent, in the sense of Baumeler and Wolf, precisely when every local intervention has a unique fixed point. No fixed point is the grandfather paradox. More than one is the bootstrap. The 2026 characterization of Dourdent, Leitherer, Boghiu, Simonov, Kunjwal and Acín says the same thing in the language of events: the event list is complete and pairwise exclusive. That is a logic of loops. It is not yet a physical theory. A physical theory needs a dynamics, and the natural quantum dynamics is unitary.

The second is the quantization question left open in 2019. Once a process function is reversible, it defines a permutation of a finite set, and every permutation defines a unitary operator on the corresponding Hilbert space. A valid unitary process is a stronger demand. Parties must be free to insert arbitrary quantum instruments, and the induced map on the remaining systems must stay completely positive and trace-preserving. The 2019 paper checked one example. The Lugano function, the standard classical process that violates a causal inequality, was later given a unitary extension by a different construction. Neither result is the universal statement. A conjecture to that effect was stated on 30 September 2026, with two sufficient conditions that are not necessary.

The implication matters for three reasons.

First, it separates logical consistency from an extra quantization postulate. If every process function lifts, then the fixed-point clause is already the quantum consistency clause. One does not need a further restriction to keep the quantum theory free of grandfather and bootstrap failures.

Second, it bears on purifiability. A unitary process is pure. A positive answer puts every classical deterministic consistent process inside the purifiable fragment, including those that violate causal inequalities. That does not settle which of them embed in a spacetime. It does settle that the obstruction, if there is one, is not unitarity.

Third, it is the right strength for a time-symmetric reading. The source-and-sink extension is already the reversible reading of the loop. A unitary dilation of that extension is an ontic time-reverse in the sense that the same operator, read backwards, is the inverse process. The reversal objection that appears when one asks the bare process function to be an involution on its own alphabet is an artifact of refusing the source and the sink.

## 2. Definitions

Let each party \(k \in \{1,\ldots,n\}\) have a finite alphabet \(A_k\) carrying a group law, written additively. The case of interest is bits under XOR. Write \(O = \prod_k A_k\) for output strings and \(I = \prod_k A_k\) for input strings. A local intervention is a tuple of functions \(f_k \colon A_k \to A_k\). A map \(w \colon O \to I\) is a process function when, for every such tuple, the composition \(f \circ w\) has exactly one fixed point.

The source-and-sink extension of Theorem 2 in Baumeler, Costa, Ralph, Wolf and Zych adds a source register \(e\) and a sink register \(s\), of the same alphabet, and sets
\[
U\lvert o, e\rangle = \lvert w(o)+e,\; o\rangle.
\]
Reading the sink off as \(o\) and the source off as \(e = i - w(o)\) inverts \(U\). So \(U\) is a permutation unitary for any \(w\), process function or not. Validity is the extra claim.

## 3. The combinatorial lemma

**Lemma.** If \(w\) is a process function and \(s \neq s'\), then some party \(k\) has \(s_k \neq s'_k\) and \(w_k(s) = w_k(s')\).

Suppose not. Then \(w_k(s) = w_k(s')\) already forces \(s_k = s'_k\). Define \(f_k\) on the two points \(w_k(s)\) and \(w_k(s')\) by \(f_k(w_k(s)) = s_k\) and \(f_k(w_k(s')) = s'_k\), and extend it arbitrarily off them. The two clauses agree wherever the inputs agree, so \(f_k\) is a function. Then \(f(w(s)) = s\) and \(f(w(s')) = s'\). Two fixed points, which a process function cannot have.

The contrapositive is the useful form. Distinct global strings that are candidates for a double fixed point must disagree, at some party, on a coordinate whose process-output value agrees.

## 4. The lift

**Theorem.** Let \(w\) be a process function, and let \(U\) be the source-and-sink permutation unitary above. For any local unitaries \(V_k\), possibly acting on a local ancilla, the source-to-sink operator induced by \(U\) is unitary. Consequently every tuple of local instruments induces a completely positive trace-preserving map from source to sink, and the Choi operator of \(U\) is a valid unitary process. Fixing the source at the identity element of the group recovers \(w\).

The matrix element, suppressing ancillas, is
\[
M_{s,e} = \prod_k \langle s_k \rvert V_k \lvert w_k(s)+e_k\rangle.
\]
Change variables by \(i_k = w_k(s)+e_k\). The sum over \(e\) becomes a sum over \(i\), and it factors across parties:
\[
(MM^\dagger)_{s,s'} = \prod_k \sum_{i_k} \langle s_k \rvert V_k \lvert i_k\rangle \langle i_k + \delta_k \rvert V_k^\dagger \lvert s'_k\rangle,
\]
with \(\delta_k = w_k(s') - w_k(s)\). If \(s = s'\), every \(\delta_k\) vanishes and each factor is a row norm, hence 1. If \(s \neq s'\), the lemma supplies a party with \(\delta_k = 0\) and \(s_k \neq s'_k\). That factor is the inner product of two distinct rows of \(V_k\), ancilla included, hence zero. Thus \(MM^\dagger = I\).

A local completely positive trace-preserving map is a unitary on a local ancilla followed by a partial trace. The partial trace of a unitary dilation is completely positive and trace-preserving. So every tuple of local instruments induces a valid map from source to sink.

The same identity explains the failures. A swap, or an identity loop, has pairs \(s \neq s'\) with no such party. The corresponding factor does not vanish, and \(MM^\dagger \neq I\). The process-function clause is what kills the shift. It is not killed by unitarity of \(\bigotimes V_k\) alone.

## 5. What the argument does not do

It does not embed the process in a spacetime. The wormhole billiard of Friedman, Morris, Novikov, Thorne and collaborators has initial data with one self-consistent motion, data with two, and data with possibly none. A process function needs one for every intervention. The unitary lift is a process-matrix statement, not a Hamiltonian embedding.

It does not say that the bare three-party function is an involution. The 2019 reversibility theorem already shows that reversibility is free only after a source and a sink are added. Of the 256 binary two-party maps, the 12 process functions are causally ordered, and none equals its input-output reverse. That tally is a certificate of the known gap, not a counterexample to the lift.

It is not kernel-checked. The combinatorial lemma is finite for any fixed alphabet and is the piece an attacker has to break. The linear algebra after it is row orthogonality.

## 6. Relation to the conjecture

Daher Ahmed and Kunjwal conjecture that every process function can be purified to a unitary process. They prove it under mutual exclusivity of control conditions, and under a second sufficient condition, unambiguity. Neither is used here. The dilation is the source-and-sink permutation unitary, and the process-function clause is the cancellation. If the lemma stands, the conjecture is a theorem, and the Lugano function is an instance rather than a special construction.

## References

1. Ä. Baumeler and S. Wolf, The space of logically consistent classical processes without causal order, New J. Phys. 18, 013036 (2016).
2. Ä. Baumeler, F. Costa, T. C. Ralph, S. Wolf and M. Zych, Reversible time travel with freedom of choice, Class. Quantum Grav. 36, 224002 (2019), arXiv:1703.00779.
3. M. Araújo, A. Feix, M. Navascués and Č. Brukner, A purification postulate for quantum mechanics with indefinite causal order, Quantum 1, 10 (2017).
4. A. Vanrietvelde, N. Ormrod, H. Kristjánsson and J. Barrett, Consistent circuits for indefinite causal order, arXiv:2206.10042 (2022).
5. H. Dourdent, A. Leitherer, E.-C. Boghiu, K. Simonov, R. Kunjwal and A. Acín, What makes a causal loop consistent?, arXiv:2609.39735 (2026).
6. N. Daher Ahmed and R. Kunjwal, Characterizing unitaries via quasi-process functions, arXiv:2610.00579 (2026).
7. J. Friedman, M. S. Morris, I. D. Novikov, F. Echeverria, G. Klinkhammer, K. S. Thorne and U. Yurtsever, Cauchy problem in spacetimes with closed timelike curves, Phys. Rev. D 42, 1915 (1990).
