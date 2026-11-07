# Classical consistency and quantum purification without a fixed causal order

**Draft for the author's review. Not submitted.** Canonical editable source: `paper/foundations.tex`. Typeset file: `paper/foundations.pdf`, built by `python3 paper/build_foundations.py`. This markdown export is for reading; if the two diverge, the TeX source wins.

**Author.** Drew Lamarr Arrowood. Affiliation, correspondence address, ORCID, funding, and competing interests: not recorded; pending confirmation. No such facts are invented here.

**Keywords.** process function; indefinite causal order; unitary process; purification; process matrix

# Introduction: consistency versus purification {#sec:intro}

A process matrix assigns a probability to every choice of local instruments, without assuming a global causal order among the laboratories [@oreshkov2012; @araujo2017]. The deterministic classical points of that theory are process functions: maps from the parties' outputs to their inputs such that every tuple of local functions has exactly one fixed point [@baumeler2016; @baumeler2019]. The fixed-point clause does two jobs at once. No fixed point is a history that contradicts itself. More than one fixed point is a history the local choices do not determine. The parties are not forbidden any local operation; only the global solution is constrained [@baumeler2019].

Two questions follow. First, does every such deterministic consistent process extend to a unitary quantum process? Baumeler, Costa, Ralph, Wolf and Zych showed that a source and a sink turn every process function into a bijection, and left open whether that bijection quantises [@baumeler2019]. Special cases were settled later: the Lugano process [@araujo2017], an $n$-party family [@araujo2017b], and unitaries with mutually exclusive control conditions [@daher2026]. The general finite-alphabet statement was formulated as a conjecture by Daher Ahmed and Kunjwal [@daher2026]. Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} below is a proof for every process function on finite alphabets, and Theorem [5](#thm:iff){reference-type="ref" reference="thm:iff"} is the converse: unitarity for every local unitary holds only for process functions.

Second, does quantum purification recover only mixtures of those deterministic processes? Mixtures do purify, by a coherent label kept at the sink. The converse was a natural conjecture and is false. Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} gives a valid three-party binary classical process, induced by an explicit pure process in the computational basis, that lies outside the convex hull of the process functions. The numerical value of the separating inequality is $\tfrac14-\tfrac{3}{16}\sqrt{2}$. The same process is known, up to a local frame, as a time-reversed variant of a Lugano purification [@guerin2018; @baumeler2019]; what is separated here is the classical process it induces in a stated basis, not the existence of the quantum board.

The article is organised as follows. Section [2](#sec:def){reference-type="ref" reference="sec:def"} fixes the finite operational setting. Section [3](#sec:lift){reference-type="ref" reference="sec:lift"} proves the lift and its converse, and records the passage from unitarity to validity. Section [4](#sec:pur){reference-type="ref" reference="sec:pur"} constructs the separation. Section [5](#sec:bounds){reference-type="ref" reference="sec:bounds"} states what the two theorems do and do not say about causal order, two parties, and spacetime. Section [6](#sec:disc){reference-type="ref" reference="sec:disc"} lists the open problems that remain inside this formalism. A short derivation of validity, the witness tables, and a note on formal verification are in the appendices. The public technical archive [@archive] contains the proofs, the machine-checked formalisation, and a large body of material deliberately omitted here.

# Operational setting and definitions {#sec:def}

Throughout the main theorems there are finitely many parties $k\in\{1,\ldots,n\}$, each with a finite nonempty input alphabet $I_k$ and a finite nonempty output alphabet $O_k$. For the permutation form of the lift we identify $I_k$ with the cyclic group $\mathbb{Z}_{|I_k|}$. The product spaces are written $O=\prod_k O_k$ and $I=\prod_k I_k$.

::: {#def:pf .definition}
**Definition 1** (Process function). A map $w=(w_k):O\to I$ is a *process function* when, for every tuple of local functions $f_k:I_k\to O_k$, the self-map of $O$ given by $$o\;\longmapsto\;\bigl(f_k(w_k(o))\bigr)_k$$ has exactly one fixed point.
:::

A fixed point is a consistent history for that intervention. The quantifier ranges over every local function, including those that are not causal functions of a background time. Acyclic deterministic circuits are process functions, but they are not all of them. The three-bit Lugano map $$\label{eq:lugano}
w(a,b,c)=(\lnot b\land c,\;\lnot c\land a,\;\lnot a\land b)$$ has a cyclic dependence and exactly one fixed point for every choice of local bit functions [@baumeler2016; @araujo2017]. For two binary parties the twelve process functions are all causally ordered [@oreshkov2012; @baumann2016].

The reversible extension uses a source, whose output space we identify with $I$, and a sink, whose input space we identify with $O$. For a basis vector $\lvert o\rangle$ of the output registers and a basis vector $\lvert e\rangle$ of the source, $$\label{eq:U}
U\lvert o\rangle_O\lvert e\rangle_P=\lvert w(o)+e\rangle_I\lvert o\rangle_F,$$ with addition in each $I_k$. For every function $w$, not only for process functions, $U$ is a permutation of a finite basis and hence unitary [@baumeler2019]. Unitarity of $U$ alone is not the quantum condition. Each party may insert a unitary that is not diagonal in the chosen basis, with a private ancilla.

::: {#def:loop .definition}
**Definition 2** (Closed loop). Let $V_k$ be a unitary from $I_k\otimes X_k$ to $O_k\otimes Y_k$, with finite ancilla spaces satisfying $|I_k|\,|X_k|=|O_k|\,|Y_k|$. Wiring each input factor of $U$ into $V_k$ and each output factor of $V_k$ back into $U$ defines an operator $M$ from $P\otimes X$ to $F\otimes Y$, $X=\bigotimes_k X_k$ and $Y=\bigotimes_k Y_k$, with matrix elements $$\label{eq:M}
M\bigl[(s,y),(e,x)\bigr]
=\prod_k V_k\bigl[(s_k,y_k),\,(w_k(s)+e_k,x_k)\bigr].$$
:::

A process is *pure* in the sense of Araújo, Feix, Navascués and Brukner when every such closed loop, for every choice of local unitaries and finite ancillas, is unitary [@araujo2017]. Purity is stronger than the existence of one unitary dilation. A classical process is *purifiable*, written $p\in\mathrm{Purif}$, when it arises from a pure process by preparing a source state, measuring each party in a stated orthonormal frame, and discarding the sink. Unless a frame is named, the frame is the computational basis. The same pure process can induce a mixture of process functions in one frame and a process outside that mixture in another [@archive]; statements below name the frame. We write $\mathrm{PF}$ for the set of process functions, $\operatorname{conv}(\mathrm{PF})$ for its convex hull, and $\mathrm{Valid}$ for the convex set of classical processes that assign total probability one under every product of local stochastic maps [@baumeler2016].

# The unitary lifting theorem {#sec:lift}

The obstruction to unitarity of $M$ is not bijectivity of $U$. It is whether distinct rows of $M$ are orthogonal after the local unitaries have been inserted. The combinatorial fact that supplies the orthogonality is pairwise exclusivity.

::: {#lem:ex .lemma}
**Lemma 3** (Exclusivity). *If $w$ is a process function and $s\neq s'$ in $O$, some party $k$ has $s_k\neq s'_k$ and $w_k(s)=w_k(s')$.*
:::

::: proof
*Proof.* Otherwise $w_k(s)=w_k(s')$ implies $s_k=s'_k$ for every $k$. Define $f_k(x)=s_k$ if $x=w_k(s)$ and $f_k(x)=s'_k$ if $x=w_k(s')$, and define $f_k$ arbitrarily elsewhere. The two clauses agree wherever the inputs agree. Then $s$ and $s'$ are distinct fixed points of one intervention. ◻
:::

The same pairing, read without quantifying over interventions, is the consistency criterion of Dourdent, Leitherer, Boghiu, Simonov, Kunjwal and Acín [@dourdent2026]. For finitely many parties and nonempty finite alphabets, exclusivity is equivalent to Definition [1](#def:pf){reference-type="ref" reference="def:pf"}. Uniqueness of a fixed point is the easy half: two fixed points of one intervention would be a pair with no exclusivity witness. Existence is an induction on the set of active parties, the others frozen at a background value. Adding party $n$, the configurations already fixed on the previous parties, for two different values of party $n$, cannot take their exclusivity witness among the frozen parties or among the parties already fixed, so the witness is party $n$ itself, and the value $f_n$ returns is independent of the trial value. That common value closes the loop. The induction is written out in the archive. The argument below uses only Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"}, which is the half that orthogonality needs.

A single intervention shows what the definition asks for in the Lugano example [\[eq:lugano\]](#eq:lugano){reference-type="eqref" reference="eq:lugano"}. Let every party return its input unchanged. A fixed point then satisfies $$a=\lnot b\land c,\qquad b=\lnot c\land a,\qquad c=\lnot a\land b.$$ If $a=1$, then $b=0$ and $c=1$, but the third equation becomes $c=0$. If $a=0$, then $b=0$ and $c=0$, and $(0,0,0)$ satisfies all three equations. Exactly one history. The same count for every other triple of local bit functions is the content of "$w$ is a process function"; it is finite and has been enumerated. The dependence is cyclic, so the example is not an acyclic circuit relabelled.

::: {#thm:lift .theorem}
**Theorem 4** (Unitary lift). *If $w$ is a process function, then for every choice of local unitaries $V_k$ and finite ancillas as in Definition [2](#def:loop){reference-type="ref" reference="def:loop"}, the closed loop $M$ is unitary.*
:::

::: proof
*Proof.* The product in [\[eq:M\]](#eq:M){reference-type="eqref" reference="eq:M"} factorises the Gram matrix. For rows $(s,y)$ and $(s',y')$, $$\label{eq:gram}
\bigl(MM^{\dagger}\bigr)\bigl[(s,y),(s',y')\bigr]
=\prod_k\sum_{e_k,x_k}
V_k\bigl[(s_k,y_k),(w_k(s)+e_k,x_k)\bigr]\,
\overline{V_k\bigl[(s'_k,y'_k),(w_k(s')+e_k,x_k)\bigr]}.$$ If $w_k(s)=w_k(s')$, the change of variables $i=w_k(s)+e_k$ makes the $k$-th factor the inner product of two rows of the unitary $V_k$. If $s=s'$, every factor is of this kind and the product is $\delta_{y,y'}$. If $s\neq s'$, Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"} supplies a party with equal inputs and unequal outputs, and that factor vanishes. Thus $MM^{\dagger}=1$. The dimension hypothesis makes $M$ square, so $M$ is unitary. ◻
:::

Column norms are not a substitute for this argument: unit-norm columns need not be orthogonal. The dimension count is the only place the ancilla sizes enter the proof of Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"}. Figure [1](#fig:lift){reference-type="ref" reference="fig:lift"} is the wiring.

Bare bijectivity of $U$ does not answer the quantum question. Equation [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is a permutation for every $w$, consistent or not. The parties are allowed to insert instruments that are not diagonal in the computational basis. A Hadamard on one wire is the simplest such instrument: it mixes the two basis states that the classical theory treated as distinct. If, after that insertion, the map from source to sink fails to be unitary, the classical fixed-point clause has not lifted, and quantum theory would be imposing an extra filter. Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} says that for a process function the filter is already in place. The rows of $M$ are orthogonal because exclusivity, not because $U$ is a permutation. Daher Ahmed and Kunjwal note that the bare permutation may fail to be a valid process and prove the lift for unitaries with mutually exclusive control conditions [@daher2026]. The factorisation [\[eq:gram\]](#eq:gram){reference-type="eqref" reference="eq:gram"} is the general case: the control conditions need not be exclusive in their sense, because the local unitaries are arbitrary and the cancellation is supplied by Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"}.

The same identity explains the ancilla quantifiers. Each $V_k$ is an arbitrary unitary between the input leg tensored with a private ancilla and the output leg tensored with a private ancilla, provided the two legs have equal finite dimension so that a unitary between them can exist. The ancillas may be entangled with each other and with the source in the incoming state. The theorem does not quantify over a single fixed ancilla dimension. It quantifies over all finite dimensions and all unitaries of those dimensions. Shared entanglement is an incoming state, not an extra hypothesis.

<figure id="fig:lift">

<figcaption>The reversible extension <span class="math inline"><em>U</em></span> and one local unitary. The sink records the output string. The source records the difference between the input and <span class="math inline"><em>w</em>(<em>o</em>)</span>.</figcaption>
</figure>

::: {#thm:iff .theorem}
**Theorem 5** (Unitarity for every local unitary characterises process functions). *Let $w:O\to I$ be any map between finite alphabets, with each $I_k$ a cyclic group as above. The closed loop $M$ is unitary for every choice of local unitaries and finite ancillas if and only if $w$ is a process function.*
:::

::: proof
*Proof.* The direction from a process function to unitarity is Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"}. Conversely, suppose some intervention $f=(f_k)$ has $N\neq 1$ fixed points, where $N=0$ and $N\ge 2$ are both allowed. Take ancillas $X_k=O_k$ and $Y_k=I_k$, and $$V_k\lvert i,x\rangle=\lvert f_k(i)+x,\,i\rangle,$$ addition in $O_k$. This is a permutation of basis states, hence unitary. The entries of column $(0,0)$ of $M$ are $$M\bigl[(s,y),(0,0)\bigr]
=\prod_k [s_k=f_k(w_k(s))]\,[y_k=w_k(s)],$$ so the squared norm of that column equals the number of fixed points of $f$. That number is not $1$, and $M$ is not an isometry. ◻
:::

The gadget uses $|I_k|\,|O_k|=|O_k|\,|I_k|$ and does not require $|I_k|=|O_k|$. The same column, read at a general ancilla index $(e,x)$, counts the fixed points of the shifted intervention $i\mapsto f(i+e)+x$. One failing test is enough for the converse. The forward direction demands that every test pass. The two directions are not the same theorem: orthogonality of rows uses exclusivity, while the column norm uses a specially chosen unitary to count solutions. A map can have unit columns for some interventions and fail orthogonality for others. Theorem [5](#thm:iff){reference-type="ref" reference="thm:iff"} is the statement that the whole family of tests passes if and only if every intervention has exactly one fixed point.

The inverse of [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is as explicit as $U$. The sink holds the output string $o$. The source, read backwards, holds the difference between the input and $w(o)$. So the classical inverse is a function of the sink and the source, not a function of the output alphabet alone. This is why a process function that is not bijective on its own alphabet, the Lugano function is two-to-one on some slices, can still have a unitary dilation. Reversibility is restored by the source and the sink, not by forcing $w$ itself to be a permutation [@baumeler2019].

Purity is unitarity under local unitaries. Validity is the trace-preserving completely positive condition under arbitrary local instruments, including instruments that share ancillas with an outside system. The passage is Stinespring's dilation and does not use any further property of $w$.

::: {#lem:valid .lemma}
**Lemma 6** (From purity to validity). *If $M$ is unitary whenever every local map is a unitary on a finite ancilla of matching dimension, then the induced process is valid under every tuple of local instruments.*
:::

::: proof
*Proof.* A local completely positive trace-preserving map dilates to an isometry into an output space tensored with an environment [@stinespring1955]. Pad the input with a junk factor and the output with a complementary factor so that the two sides have equal finite dimension, and extend the isometry to a unitary by completing orthonormal bases. Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} supplies a unitary on the enlarged loop. The environments are prepared in a fixed state and then discarded. Partial trace and a fixed ancilla state preserve the trace and complete positivity, and the link product is multilinear, so the original instruments yield a trace-preserving completely positive map from the source to the sink. An instrument is a family of such maps. The same identity, applied to the Choi operator of $U$, is the process-matrix normalisation $\operatorname{Tr} W=1$ on the accepted local maps [@araujo2017; @choi1975]. ◻
:::

The finite-dimensional argument is machine-checked in the archive, including instruments and shared ancillas. Extending the alphabets from finite to arbitrary discrete sets replaces the matrix calculation by an $\ell^2$ argument; that extension is in the archive and is not needed here. Continuous alphabets are a different problem, because a single history is typically a null set, and they are only partly treated in the archive.

One example is enough to see that the lift is not confined to causal order. The Lugano function [\[eq:lugano\]](#eq:lugano){reference-type="eqref" reference="eq:lugano"} is a process function, so Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} supplies a unitary process. Its dependence graph is a cycle. The dilation does not remove the cycle. It realises the cycle as a unitary from a source to a sink.

# Quantum purification exceeds deterministic mixtures {#sec:pur}

A mixture of process functions is purifiable. If $w^{(j)}$ has weight $\lambda_j$, prepare a control register in $\sum_j\sqrt{\lambda_j}\lvert j\rangle$ and route the control unchanged to the sink, while the system register carries the reversible extension of $w^{(j)}$ controlled on $j$. The closed loop is block diagonal in the control basis with unitary blocks, hence unitary. Discarding the sink and reading the computational basis leaves the classical mixture. The same block-diagonal sum shows that $\mathrm{Purif}$ is convex. This is the coherent form of an inclusion that had been asserted for the dephased process matrix [@baumeler2022]. The argument just given is for the coherent operator.

The converse, that nothing else is purifiable, was a conjecture of the technical archive. It is false.

::: {#thm:sep .theorem}
**Theorem 7** (A purifiable classical process outside the process-function hull). *There exists a valid classical process $p$ on three binary parties, induced in the computational basis by a pure process with a finite source, such that $$\label{eq:L}
L(p)=\frac14-\frac{3}{16}\sqrt{2}<0,$$ while $L\ge 0$ on every process function and hence on $\operatorname{conv}(\mathrm{PF})$. In particular $\operatorname{conv}(\mathrm{PF})\subsetneq\mathrm{Purif}$.*
:::

The witness is a switchboard. For each output string $o\in\{0,1\}^3$ there is a unitary $U_o$ on $(\mathbb{C}^2)^{\otimes 3}$. Let $H$ be the three-qubit Hadamard and let $m_o(z)\in\{0,1,2,3\}$ be the exponents in Appendix [8](#app:witness){reference-type="ref" reference="app:witness"}, indexed by $z\in\{0,1\}^3$ in binary order. Set $$\label{eq:Uo}
U_o=H\,\mathrm{diag}\bigl(i^{m_o(z)}\bigr)\,H,$$ so $U_o$ is diagonal in the Hadamard basis. The pure vector is $$\label{eq:V}
V\lvert o,s,t\rangle
=\sum_e U_o[e,s]\,\lvert e\rangle_I\lvert o\rangle_F\lvert e\oplus t\rangle_F.$$ The source state is $\phi\otimes\lvert 0\rangle$, with $$\label{eq:phi}
\phi=\frac{\lvert 011\rangle+e^{-i\pi/4}\lvert 100\rangle}{\sqrt{2}},$$ and the classical process is the computational-basis conditional distribution $p(i\mid o)=\lvert\langle i\rvert U_o\phi\rvert^2$.

Three facts have to be checked, and they have different proofs.

First, $p$ is a valid classical process: it is nonnegative, and every product of local stochastic maps has total probability one. For deterministic local functions this is a finite sum, sixty-four of them, one for each triple of functions from a bit to a bit. The sum is multilinear in the three local operations. Every stochastic local map is a convex combination of deterministic ones, so a multilinear identity that holds on the deterministic vertices holds for every product of stochastic maps. The entries of $p$ lie in $\mathbb{Q}(\sqrt{2})$ and each column sums to one. Both the direct expansion and an independent re-derivation from the definition of $V$ confirm the identity in exact arithmetic; the archive records the scripts. Floating-point circuit simulations reproduce the same table to roundoff and are checks, not proofs.

Second, $V$ is pure. The mechanism is the same exclusivity that appeared in Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"}, now for a sum of basis permutations rather than for one. Compare the boards $U_o$ and $U_{o'}$ for two different output strings. Their mismatch is the unitary $K=U_o U_{o'}^{\dagger}$. Expanded in the Pauli basis of three qubits, every term that appears with a nonzero coefficient must act as the identity on at least one party whose output bit differs between $o$ and $o'$. A single process function has a mismatch that is one Pauli string, and the condition reduces to Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"}. A switchboard may superpose several such strings, each leaving a different party alone. For the exponents in Table [1](#tab:m){reference-type="ref" reference="tab:m"} that cancellation is an identity in the cyclotomic field $\mathbb{Q}(\zeta_8)$: every forbidden coefficient is zero. There are $2232$ of them, a finite exact check, not a sample.

That Pauli condition is the no-ancilla half of purity. Ancillas can only enlarge the set of parties whose local data differ between two rows, and a signed sum over a larger set of bits is a sum of signed sums over subsets. Vanishing on the smaller sets implies vanishing on the larger ones. The diagonal case, equal outputs, reduces to orthonormality of the local bases. With that lemma, purity with finite ancillas is the same list of coefficients as purity without them. The lemma is general for this switchboard shape; the numerical content special to the witness is the vanishing of the coefficients. Both are proved in the archive. A second route, used by the machine-checked formalisation, never invokes the lemma. It proves $MM^{\dagger}=1$ for this specific $V$ by reducing, by multilinearity, to finitely many combinations of local slots and checking those. A third script checks the same multilinear identity directly from the matrix entries. Any one of the three supports purity for Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"}. The formalisation additionally identifies purity with unitarity of the link product in the process-matrix definition, and extends purity for this machine from finite ancillas to ancillas in arbitrary Hilbert spaces. Those extensions are cited, not re-proved here. What the present article uses is purity under finite ancillas together with the classical distribution [\[eq:phi\]](#eq:phi){reference-type="eqref" reference="eq:phi"}.

Third, $p\notin\operatorname{conv}(\mathrm{PF})$. The integer table $g_{io}$ of Appendix [8](#app:witness){reference-type="ref" reference="app:witness"}, with rows $i$ and columns $o$, defines $$\label{eq:g}
L(q)=\sum_{i,o} g_{io}\,q(i\mid o).$$ On the witness, $L(p)=\tfrac14-\tfrac{3}{16}\sqrt{2}$. On each of the $744$ binary three-party process functions, $L\ge 0$, and the bound is tight on $418$ of them. Both evaluations are exact. Nonnegativity on the vertices implies nonnegativity on the convex hull, so $p\notin\operatorname{conv}(\mathrm{PF})$. The archive's formalisation proves the same strict inequality and the nonmembership; it does not, by itself, prove that $L$ is a facet inequality or that there are exactly $744$ process functions. The count $744$ is the exhaustive enumeration of Definition [1](#def:pf){reference-type="ref" reference="def:pf"} on three bits, re-done by an independent script. The facet language in the archive means that $L$ came from a facet of the hull; Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} needs only that $L$ separates.

The linear-programming distance from $p$ to $\operatorname{conv}(\mathrm{PF})$ in the sum of absolute values over the $64$ entries is a floating-point figure, about $0.0607$, and is not part of the proof. The inequality $L$ certifies a smaller, exact margin.

The board [\[eq:Uo\]](#eq:Uo){reference-type="eqref" reference="eq:Uo"} is not a new quantum process in every local frame. It is a frame-rotated time reverse of the Lugano purification in which one party's conditional bit flip is replaced by its square root [@guerin2018; @archive]. Read in the computational basis, the induced classical process lies outside $\operatorname{conv}(\mathrm{PF})$. Read in another basis, a known pure process of this family can induce a mixture of process functions. The separation is a statement about a named frame. It is not a claim to have discovered the underlying unitary board, and it is not a claim that the board fails to be a purification of any process function in every frame.

# Physical significance and boundaries {#sec:bounds}

Classically reversible purification is a different relation. If the purifying object is itself a classical bijection, the induced classical process is a mixture of process functions. The proof is in the archive. Together with Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} it says that the gap is quantum: a coherent sum of board unitaries, not a classical mixture of bijections, produces the extra statistics.

The gap needs three parties. For two parties, every valid classical process is a mixture of causally ordered process functions. That bipartite fact is standard [@oreshkov2012; @baumann2016]; the archive re-proves it for arbitrary finite alphabets. Three parties are also the smallest setting in which a process function can violate a causal inequality, the Lugano example [\[eq:lugano\]](#eq:lugano){reference-type="eqref" reference="eq:lugano"}. Causal inequality violation and lying outside $\operatorname{conv}(\mathrm{PF})$ are not the same phenomenon. Lugano is a process function, so it lies in $\operatorname{conv}(\mathrm{PF})$, and it violates causal inequalities. The witness of Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} lies outside $\operatorname{conv}(\mathrm{PF})$. Whether that witness violates a device-independent causal inequality is a separate calculation; the archive records that a related four-term board does, and that the question for the witness of Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} is not the theorem itself. Nothing in this article is a new causal inequality.

There is a structural reason the witness could exist. If in some purification a party is first at the operator level, its input prepared from the source alone, the induced classical process is a mixture of process functions. The same conclusion holds when a party is last, or first with valid bipartite conditionals. The witness of Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} has no operator-first party: each party's input depends on another party's output. These structural theorems are proved in the archive. They explain where a counterexample had to sit. They are not re-derived here.

The lift is not a spacetime theorem. A unitary process on a finite alphabet is not a solution of Einstein's equation and not a local Hamiltonian flow on a wormhole. Post-selection can simulate the event list conditional on success; that is a filter on samples, not the dilation. Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} says that a consistent list of local events has a unitary dilation in the process theory. It does not say that the dilation embeds in a relativistic spacetime [@vilasini2024].

Purity does not mean "mixture of deterministic consistent processes." It does exclude some classically valid processes. The archive contains exact non-purifiability certificates for one extremal point of the classical polytope and for two orbits of vertices. Those certificates are not reproduced in this article. If they are granted, $\mathrm{Purif}$ sits strictly between $\operatorname{conv}(\mathrm{PF})$ and $\mathrm{Valid}$. If they are not, Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} still gives the one strict inclusion $\operatorname{conv}(\mathrm{PF})\subsetneq\mathrm{Purif}$, and convexity of $\mathrm{Purif}$ gives the mixtures of that witness.

Finally, the finite-party hypothesis is essential for reading exclusivity as existence of a history. With infinitely many parties, pairwise exclusivity still yields at most one fixed point. If each local map depends continuously on the outputs, it yields exactly one. Without continuity, ZFC provides an explicit exclusive self-map of $\{0,1\}^{\mathbb{N}}$ with no fixed point, so the corresponding infinite-party $w$ is not a process function. The general question whether every exclusive Baire-class-one self-map of that space has a fixed point is open. Neither fact is used in Theorems [4](#thm:lift){reference-type="ref" reference="thm:lift"}--[7](#thm:sep){reference-type="ref" reference="thm:sep"}. They mark the boundary of the finite theory.

The two theorems answer different physical questions and should not be collapsed. Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} says that a deterministic consistent loop, in the exact fixed-point sense, already has a coherent unitary realisation. Nothing quantum is added by hand beyond the local instruments. Theorem [7](#thm:sep){reference-type="ref" reference="thm:sep"} says that if one starts from the quantum side and reads out a classical process in a fixed basis, the processes one obtains are not exhausted by mixtures of those deterministic loops. Purity is doing less selective work on the classical side than the fixed-point clause does on the deterministic side. The inclusion $\operatorname{conv}(\mathrm{PF})\subseteq\mathrm{Purif}$ is the coherent label in the source. The failure of the reverse inclusion is one three-party matrix and one linear functional.

A process function that violates a causal inequality already has each party's input depending on another party's output. The later laboratory is an argument of the earlier input. That is a cycle in the functional dependence. It is not, by itself, a hidden variable propagating from the future, and it is not a solution of a retrocausality no-go. The dilation makes the cycle reversible by adding a source and a sink whose roles exchange under the inverse of $U$. Whether that exchange is the time symmetry asked for in other programmes is a reading of the same operator. The mathematics forces the reading to name a frame and a source state before it says anything about classical statistics. It removes one cheap reply: one cannot say that the cyclic classical model disappears as soon as the instruments are unitary.

# Discussion and conclusion {#sec:disc}

Within the process theory, deterministic consistency is already a quantum condition. For every finite process function the canonical permutation, tested against every local unitary and every finite ancilla, remains unitary, and validity under instruments follows by dilation. The same family of tests fails exactly when some local choice has the wrong number of histories. Consistency is necessary, not an optional regularity.

Purity does not, in addition, cut the classical processes back down to mixtures of those histories. Three binary parties, one coherent switchboard, and one linear inequality are enough to separate the two sets. The inequality is exact. The purity of the witness is proved both by a Pauli cancellation and by a direct expansion, and it is machine-checked. The classical distribution is computed in the computational basis and is valid.

What remains open, inside the same definitions, is the shape of $\mathrm{Purif}$: whether it is a polytope, which further vertices of $\mathrm{Valid}$ it contains, and which facet inequalities of $\operatorname{conv}(\mathrm{PF})$ survive on every purifiable process. Several such inequalities are settled on large families in the archive and left open on $\mathrm{Purif}$ as a whole; those calculations are not part of the argument above. Also open is a completed description of continuous alphabets, where fixed points are no longer isolated basis vectors. The infinite-party and Baire-class questions of the archive are boundaries of the combinatorial lemma, not further hypotheses of Theorems [4](#thm:lift){reference-type="ref" reference="thm:lift"} and [7](#thm:sep){reference-type="ref" reference="thm:sep"}.

The manuscript is a draft drawn from a public technical archive. It has not been submitted and has not been peer reviewed.

# Statements and declarations {#statements-and-declarations .unnumbered}

#### Funding.

Not yet confirmed by the author. No funding statement should be inferred.

#### Competing interests.

Not yet confirmed by the author. No declaration of absence of conflict should be inferred.

#### Author contribution.

The mathematical results summarised here are those of the public technical archive by Drew Lamarr Arrowood. This condensation was drafted with generative assistance, as disclosed below, and awaits the author's verification.

#### Data availability.

All constructions used in the proofs are in this article or in the public archive [@archive], commit `154eec4` (full identifier `154eec44e2b26b12d4e0f091185a0e9f70750c4c`). The witness unitaries are Table [1](#tab:m){reference-type="ref" reference="tab:m"} and equations [\[eq:Uo\]](#eq:Uo){reference-type="eqref" reference="eq:Uo"}--[\[eq:phi\]](#eq:phi){reference-type="eqref" reference="eq:phi"}. The separating coefficients are Table [2](#tab:g){reference-type="ref" reference="tab:g"}. Exact arithmetic scripts live in `code/stochastic/cyclic/switchboard/c1/` and `code/stochastic/cyclic/switchboard/verify_h12/` of that archive. The machine-checked statements cited in Appendix [9](#app:lean){reference-type="ref" reference="app:lean"} are under `lean/PFUL/`, Lean 4.34.1 and Mathlib `v4.34.1`. No experimental data were generated.

#### Ethics approval and consent.

Not applicable: the work is theoretical.

#### Use of generative assistance.

Organisation of this draft, including wording of proofs whose mathematical content is taken from the archive, was assisted by Grok Bot, a Cursor cloud agent. The assistance was not limited to copy editing. The assistant is not an author. Large language models do not meet authorship criteria. The human author remains responsible for the text; author verification of this draft is pending.

# Acknowledgments {#acknowledgments .unnumbered}

Pending the author's text. None are invented here.

# From local instruments to the closed loop {#app:valid}

This appendix spells out the bookkeeping in Lemma [6](#lem:valid){reference-type="ref" reference="lem:valid"}. Let $A_k$ be a completely positive trace-preserving map from states on $I_k\otimes X_k$ to states on $O_k\otimes Y_k$. Stinespring's theorem [@stinespring1955] gives an isometry $S_k:I_k\otimes X_k\to O_k\otimes Y_k\otimes E_k$ with $A_k(\rho)=\operatorname{Tr}_{E_k}(S_k\rho S_k^{\dagger})$. Choose finite junk spaces $E'_k$ and $E''_k$ so that $$|I_k|\,|X_k|\,|E'_k|=|O_k|\,|Y_k|\,|E_k|\,|E''_k|.$$ The isometry $\psi\otimes\lvert 0\rangle\mapsto (S_k\psi)\otimes\lvert 0\rangle$ on the vacuum slice of $E'_k$ extends to a unitary $V_k$ between these spaces. Then $$A_k(\rho)=\operatorname{Tr}_{E_k E''_k}\Bigl(V_k\bigl(\rho\otimes\lvert 0\rangle\langle 0\rvert\bigr)V_k^{\dagger}\Bigr).$$ Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} applies to the family $V_k$, because $w$ is a process function. The link product with $U$ is multilinear and commutes with adjoining a fixed state on a factor that $U$ does not contract, and with the partial trace over such a factor. Discarding $E_k E''_k$ therefore leaves a completely positive trace-preserving map. An instrument is handled term by term. Shared entanglement sits in the joint state of the source and the input ancillas; the hypothesis of Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} quantifies over all local unitaries and does not require the ancillas to start uncorrelated.

The argument uses finite dimension to complete the isometry to a unitary. The archive treats the infinite-dimensional bookkeeping separately and lists the caveats that remain for non-trace-class Choi operators. Those caveats do not affect Theorems [4](#thm:lift){reference-type="ref" reference="thm:lift"} and [7](#thm:sep){reference-type="ref" reference="thm:sep"} as stated for finite alphabets and finite ancillas.

One direction of the dilation is worth separating from the other. Purity assumes unitaries and concludes unitarity. Validity assumes completely positive trace-preserving maps and concludes the same for the global map. The step from the first to the second is not the slogan that every unitary is valid. A unitary dilation of each local map, on a larger space, is fed to the purity hypothesis, and the environments are then discarded. Discarding is what produces a general instrument from a unitary. If the environments were kept, one would still have only the unitary case. Lemma [6](#lem:valid){reference-type="ref" reference="lem:valid"} is that discarding step, together with the dimension padding that lets Theorem [4](#thm:lift){reference-type="ref" reference="thm:lift"} apply. It is special to finite dimension in the form written here.

# Witness tables {#app:witness}

Table [1](#tab:m){reference-type="ref" reference="tab:m"} is the list of exponents $m_o(z)$ in [\[eq:Uo\]](#eq:Uo){reference-type="eqref" reference="eq:Uo"}. Columns run over $z=000,\ldots,111$ in binary order.

::: {#tab:m}
   $o$   $m_o(z)$                          
  ----- ---------- --- --- --- --- --- --- ---
   000      0       3   0   0   2   0   3   0
   001      0       3   2   2   2   0   3   0
   010      0       3   0   0   2   1   3   1
   011      0       3   2   2   2   1   3   1
   100      0       1   2   2   2   2   1   2
   101      0       1   0   0   2   2   1   2
   110      0       1   2   2   2   3   1   3
   111      0       1   0   0   2   3   1   3

  : Exponents $m_o(z)\in\{0,1,2,3\}$ for the witness unitaries. Rows are output strings $o$.
:::

Table [2](#tab:g){reference-type="ref" reference="tab:g"} is the integer kernel of $L$ in [\[eq:g\]](#eq:g){reference-type="eqref" reference="eq:g"}, copied from the formalisation, where it is stored as `gTab` with rows $i$ and columns $o$. The constant term is zero. The identity $L(p)=\tfrac14-\tfrac{3}{16}\sqrt{2}$ is the evaluation of this table on $p(i\mid o)=\lvert\langle i\rvert U_o\phi\rvert^2$. Equivalently, if $p=(p_N+p_M\sqrt{2})/128$ in the monomial basis used by the formalisation, then $\sum g_{io}p_N=32$ and $\sum g_{io}p_M=-24$.

::: {#tab:g}
   $i\backslash o$    000    001    010   011    100   101    110   111
  ----------------- ----- ------ ------ ----- ------ ----- ------ -----
         000            0      0      0     0      0     0      0     0
         001            1   $-1$      0     0      0     0      0     0
         010            1      0   $-1$     0      0     0      0     0
         011            1      0      0     0      0     0      0     0
         100            1      0      0     0   $-1$     0      0     0
         101            2      0      0     0   $-1$     0      0     0
         110            1      0      0     0      0     0   $-1$     0
         111            2      0      0     0      0     0      0     0

  : Separating coefficients $g_{io}$. Row $i$, column $o$, binary order $000,\ldots,111$.
:::

Nonnegativity of $L$ on process functions is a finite check: either the five relevant output strings already make $L\ge 0$, or one of four explicit interventions has two fixed points among them. The formalisation encodes that case split and evaluates it in the kernel. An independent script re-enumerates all $8^8$ maps, retains the process functions, and evaluates both $L$ and a second rational separator $1-\tfrac34\sqrt{2}<0$.

# Formal verification {#app:lean}

The following statements in the public archive are machine-checked in Lean 4.34.1 with Mathlib `v4.34.1`. The only axioms reported for them are propositional extensionality, the axiom of choice, and quotient soundness. There is no `sorry`. Finite combinatorial searches inside the development use kernel reduction rather than native evaluation. A check of this kind certifies the formal statement, not the informal gloss and not a laboratory realisation.

The lift and the converse for finite alphabets are the archive declarations `induced_unitary` and `unitary_iff_pf` in the copy-gadget development. The validity package, including instruments and the process-matrix normalisation, is the declaration `validity_package`. The separation is the declaration `purification_conjecture_false`: there exists a classical $p$ that is valid, purifiable, and outside the convex hull of the process functions, with $L(p)=(32-24\sqrt{2})/128$. The same theorem is restated with process-matrix definitions. Build instructions and the map from paper statements to names are in the archive file `lean/STATUS.md` and in its Appendix M. The further formalised lemmas in that appendix, including the infinite-party development, are not dependencies of Theorems [4](#thm:lift){reference-type="ref" reference="thm:lift"}--[7](#thm:sep){reference-type="ref" reference="thm:sep"}.

::: thebibliography
99

O. Oreshkov, F. Costa, and Č. Brukner, Quantum correlations with no causal order, Nature Communications **3**, 1092 (2012). <https://doi.org/10.1038/ncomms2076>

Ä. Baumeler and S. Wolf, The space of logically consistent classical processes without causal order, New Journal of Physics **18**, 013036 (2016). <https://doi.org/10.1088/1367-2630/18/1/013036>

Ä. Baumeler, F. Costa, T. C. Ralph, S. Wolf, and M. Zych, Reversible time travel with freedom of choice, Classical and Quantum Gravity **36**, 224002 (2019), arXiv:1703.00779.

M. Araújo, A. Feix, M. Navascués, and Č. Brukner, A purification postulate for quantum mechanics with indefinite causal order, Quantum **1**, 10 (2017). <https://doi.org/10.22331/q-2017-04-25-10>

M. Araújo, P. A. Guérin, and Ä. Baumeler, Quantum computation with indefinite causal structures, Physical Review A **96**, 052315 (2017), arXiv:1706.09854. <https://doi.org/10.1103/PhysRevA.96.052315>

N. Daher Ahmed and R. Kunjwal, Characterizing unitaries via quasi-process functions, arXiv:2610.00579 (2026).

H. Dourdent, A. Leitherer, E.-C. Boghiu, K. Simonov, R. Kunjwal, and A. Acín, What makes a causal loop consistent?, arXiv:2609.39735 (2026).

Ä. Baumeler, A. S. Gilani, and J. Rashid, Unlimited non-causal correlations and their relation to non-locality, Quantum **6**, 673 (2022). <https://doi.org/10.22331/q-2022-03-29-673>

P. A. Guérin and Č. Brukner, Observer-dependent locality of quantum events, New Journal of Physics **20**, 103031 (2018), arXiv:1805.12429. <https://doi.org/10.1088/1367-2630/aae742>

V. Baumann and Č. Brukner, Appearance of causality in process matrices when performing fixed-basis measurements for two parties, Physical Review A **93**, 062324 (2016). <https://doi.org/10.1103/PhysRevA.93.062324>

W. F. Stinespring, Positive functions on $C^{*}$-algebras, Proceedings of the American Mathematical Society **6**, 211 (1955). <https://doi.org/10.1090/S0002-9939-1955-0069403-4>

M.-D. Choi, Completely positive linear maps on complex matrices, Linear Algebra and its Applications **10**, 285 (1975). <https://doi.org/10.1016/0024-3795(75)90075-0>

V. Vilasini and R. Renner, Embedding cyclic information-theoretic structures in acyclic spacetimes: no-go results for indefinite causality, Physical Review A **110**, 022227 (2024), arXiv:2203.11245. <https://doi.org/10.1103/PhysRevA.110.022227>

D. L. Arrowood, Every process function lifts to a unitary process, public technical archive, <https://github.com/drewarrowood/process-function-unitary-lift>, commit `154eec44e2b26b12d4e0f091185a0e9f70750c4c`; readable version <https://drewarrowood.github.io/process-function-unitary-lift/>.
:::

[^1]: Affiliation and correspondence address: pending confirmation by the author. ORCID: not recorded in the source manuscript. This file is a draft for the author's review. It has not been submitted.
