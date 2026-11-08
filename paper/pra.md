# Statement {#sec:statement}

The object of this note is one equivalence and one separation, both finite. They are the same mathematical statements as in the author's public technical note [@archive]. This file is an alternative write-up for a physics audience. It is not an independent discovery, and it does not survey the literature beyond the works cited for the definitions it uses.

Let each party $k$ have finite nonempty alphabets $I_k$ and $O_k$, and write $I=\prod_k I_k$ and $O=\prod_k O_k$. A map $w=(w_k):O\to I$ is a process function when, for every tuple of functions $f_k:I_k\to O_k$, the self-map $o\mapsto(f_k(w_k(o)))_k$ of $O$ has exactly one fixed point [@baumeler2016]. Identify each $I_k$ with a cyclic group of order $|I_k|$ when a sum in that alphabet is required. For every map $w$, not only for process functions, the canonical extension is the basis permutation $$\label{eq:U}
U\lvert o\rangle_O\lvert e\rangle_P=\lvert w(o)+e\rangle_I\lvert o\rangle_F.$$ Let $V_k$ be unitary from $I_k\otimes X_k$ to $O_k\otimes Y_k$ with $|I_k|\,|X_k|=|O_k|\,|Y_k|$ and with $X_k,Y_k$ finite-dimensional. The closed loop $M$, from $P\otimes\bigotimes_k X_k$ to $F\otimes\bigotimes_k Y_k$, has matrix elements $$\label{eq:M}
M\bigl[(s,y),(e,x)\bigr]
=\prod_k V_k\bigl[(s_k,y_k),(w_k(s)+e_k,x_k)\bigr].$$ Call $w$ pure, for this extension, when every such $M$ is unitary. This is the purity condition of Araújo, Feix, Navascués, and Brukner, specialized to the family [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} [@araujo2017].

::: {#thm:iff .theorem}
**Theorem 1**. *The operator $M$ in Eq. [\[eq:M\]](#eq:M){reference-type="eqref" reference="eq:M"} is unitary for every local unitary and every matched finite ancilla if and only if $w$ is a process function.*
:::

Equation [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is unitary for every $w$. Theorem [1](#thm:iff){reference-type="ref" reference="thm:iff"} is therefore not the statement that a reversible encoding exists. It is the statement that the closed loop stays unitary under the whole family of local unitaries. The theorem does not say that an arbitrary dilation of an arbitrary channel is unitary only for process functions. The converse proved below uses one explicit family of local unitaries.

A second, separate statement uses a known board. It is a frame-rotated time reverse of a Lugano purification in the family of Guérin and Brukner, with one conditional bit flip replaced by a square root of that flip [@guerin2018]. It is not a new device.

::: {#thm:sep .theorem}
**Theorem 2**. *There is a conditional distribution $p(i\mid o)$ on three binary parties, obtained by reading the computational basis of that board, such that $$\label{eq:L}
L(p)=\frac14-\frac{3}{16}\sqrt{2}<0,$$ while $L\ge 0$ on every three-bit process function in an enumeration recorded elsewhere. Hence $p$ is not a convex mixture of those process functions.*
:::

The sign of $L(p)$ is proved in this file from Tables [1](#tab:m){reference-type="ref" reference="tab:m"} and [2](#tab:g){reference-type="ref" reference="tab:g"}. The inequality $L\ge 0$ on process functions is not. Section [3](#sec:witness){reference-type="ref" reference="sec:witness"} states the division of labor.

# Proof of the equivalence {#sec:proof}

::: {#lem:ex .lemma}
**Lemma 3**. *If $w$ is a process function and $s\neq s'$ in $O$, some party $k$ has $s_k\neq s'_k$ and $w_k(s)=w_k(s')$.*
:::

::: proof
*Proof.* Otherwise $w_k(s)=w_k(s')$ implies $s_k=s'_k$ for every $k$. Define $f_k(x)=s_k$ if $x=w_k(s)$ and $f_k(x)=s'_k$ if $x=w_k(s')$, and define $f_k$ arbitrarily on the rest of $I_k$. The two clauses agree where the inputs coincide. Then $s$ and $s'$ are distinct fixed points of one tuple $(f_k)$. ◻
:::

::: {#lem:forward .lemma}
**Lemma 4**. *If $w$ is a process function, then $M$ is unitary for every choice of local unitaries and matched finite ancillas.*
:::

::: proof
*Proof.* The Gram matrix of the rows is $$\label{eq:gram}
\begin{split}
&\bigl(MM^{\dagger}\bigr)\bigl[(s,y),(s',y')\bigr]\\
&\quad=\prod_k\sum_{e_k,x_k}
V_k\bigl[(s_k,y_k),(w_k(s)+e_k,x_k)\bigr]\\
&\qquad\times\overline{V_k\bigl[(s'_k,y'_k),(w_k(s')+e_k,x_k)\bigr]}.
\end{split}$$ If $w_k(s)=w_k(s')$, the change of variables $i=w_k(s)+e_k$ makes the $k$th factor the inner product of two rows of the unitary $V_k$. If $s=s'$, every factor is of this kind and the product is $\delta_{y,y'}$. If $s\neq s'$, Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"} supplies a party whose factor vanishes. Thus $MM^{\dagger}=1$. Matched dimensions make $M$ square, so $M$ is unitary. ◻
:::

Column norms are not a substitute for this argument: unit-norm columns need not be orthogonal. Ancilla dimensions enter Lemma [4](#lem:forward){reference-type="ref" reference="lem:forward"} only through squareness. The parties may share entanglement in the ancillas before the local unitaries act; the matrix element [\[eq:M\]](#eq:M){reference-type="eqref" reference="eq:M"} does not assume a product ancilla state. The state on $P$ is not part of the unitarity claim.

::: proof
*Proof of Theorem [1](#thm:iff){reference-type="ref" reference="thm:iff"}.* Lemma [4](#lem:forward){reference-type="ref" reference="lem:forward"} is one direction. Conversely, suppose a tuple $f$ has $N\neq 1$ fixed points. Take $X_k=O_k$, $Y_k=I_k$, and $$\label{eq:Vk}
V_k\lvert i,x\rangle=\lvert f_k(i)+x,\,i\rangle.$$ Each $V_k$ is a permutation of a finite basis, hence unitary, and the dimensions match. The entries of column $(0,0)$ of $M$ are $$M\bigl[(s,y),(0,0)\bigr]
=\prod_k [s_k=f_k(w_k(s))]\,[y_k=w_k(s)],$$ using Iverson brackets. The squared norm of that column equals the number of fixed points, which is $N\neq 1$. Hence $M$ is not an isometry. ◻
:::

The local unitaries [\[eq:Vk\]](#eq:Vk){reference-type="eqref" reference="eq:Vk"} are diagonal in a shifted computational basis. The forward direction quantifies over every local unitary, including those that are not diagonal in that basis. Both directions are required for the stated equivalence.

::: {#lem:valid .lemma}
**Lemma 5**. *If $M$ is unitary for every local unitary on a matched finite ancilla, then every tuple of local finite-dimensional instruments induces a trace-preserving completely positive map from the source side to the sink side.*
:::

::: proof
*Proof.* A local completely positive trace-preserving map dilates to an isometry on a finite environment [@stinespring1955]. Pad both sides with finite junk spaces so the dilated map has equal finite input and output dimension, and extend the isometry to a unitary. Lemma [4](#lem:forward){reference-type="ref" reference="lem:forward"} supplies a unitary on the enlarged loop. Discard the environments. Partial trace preserves complete positivity and, for a trace-preserving dilation, the trace. The link product is multilinear, so the original instruments yield a trace-preserving completely positive map. ◻
:::

The padding step uses finite dimension. Nothing is claimed for continuous alphabets. With infinitely many parties, the exclusivity argument of Lemma [3](#lem:ex){reference-type="ref" reference="lem:ex"} still yields at most one fixed point, while existence can fail. Whether every exclusive Baire-class-one self-map of $\{0,1\}^{\mathbb{N}}$ has a fixed point is open. That question is not used in Theorems [1](#thm:iff){reference-type="ref" reference="thm:iff"} or [2](#thm:sep){reference-type="ref" reference="thm:sep"}.

Two binary examples fix the quantifiers in the definition, without adding a theorem. If one party copies a bit and the other flips it, no output pair is a fixed point. If the second party copies the bit, both values are fixed points. Neither map is a process function, while Eq. [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is still a permutation. The three-bit rule $w(a,b,c)=(\lnot b\land c,\lnot c\land a,\lnot a\land b)$ is a process function [@baumeler2016]: every substitution of local bit functions has one history. For the three identity functions the history is $(0,0,0)$.

# Witness in one basis {#sec:witness}

Mixtures of process functions are purifiable by a label. Prepare $\sum_j\sqrt{\lambda_j}\lvert j\rangle$, apply the extension [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} of the selected process function controlled on $j$, and send the label to the sink. The loop is block diagonal with unitary blocks. Reading the computational basis and discarding the sink leaves the mixture. The converse is the content of Theorem [2](#thm:sep){reference-type="ref" reference="thm:sep"}, and only in a named basis.

For each output string $o\in\{0,1\}^3$ let $H$ be the three-qubit Hadamard gate, the tensor product of three single-qubit Hadamard gates, and let $m_o(z)\in\{0,1,2,3\}$ be Table [1](#tab:m){reference-type="ref" reference="tab:m"}, with $z$ in binary order from $000$ to $111$. Set $$\label{eq:Uo}
U_o=H\,\mathrm{diag}\bigl(i^{m_o(z)}\bigr)\,H.$$ The source vector on the three qubits is $$\label{eq:phi}
\phi=\frac{\lvert 011\rangle+e^{-i\pi/4}\lvert 100\rangle}{\sqrt{2}},$$ and $$\label{eq:p}
p(i\mid o)=\lvert\langle i\rvert U_o\phi\rvert^2.$$ The functional $L$ has integer coefficients $g_{io}$ in Table [2](#tab:g){reference-type="ref" reference="tab:g"}, rows $i$ and columns $o$, and $L(p)=\sum_{i,o}g_{io}\,p(i\mid o)$.

Direct expansion of Eqs. [\[eq:Uo\]](#eq:Uo){reference-type="eqref" reference="eq:Uo"}--[\[eq:p\]](#eq:p){reference-type="eqref" reference="eq:p"} in the field $\mathbb{Q}(i,\sqrt{2})$, followed by contraction with Table [2](#tab:g){reference-type="ref" reference="tab:g"}, produces Eq. [\[eq:L\]](#eq:L){reference-type="eqref" reference="eq:L"}. Equivalently, if each probability is written so that $128\,p(i\mid o)$ lies in $\mathbb{Z}[\sqrt{2}]$, the same contraction gives $$\sum_{i,o}g_{io}\,128\,p(i\mid o)=32-24\sqrt{2},$$ and dividing by $128$ is Eq. [\[eq:L\]](#eq:L){reference-type="eqref" reference="eq:L"}. This evaluation was repeated for the present draft from the printed tables. It does not depend on the enumeration discussed next.

Three further claims are not proved in this file.

Validity of $p$ as a classical process, meaning nonnegativity and normalization under every product of local stochastic maps, is a finite multilinear identity on the sixty-four deterministic local bit functions. The identity is recorded in the public repository [@archive]. The terms are not expanded here.

Purity of the switchboard, in one route recorded in that repository, is the vanishing of $2232$ Pauli coefficients in $\mathbb{Q}(\zeta_8)$, together with a lemma that finite ancillas do not create new failures for this shape of board. A second route reduces $MM^{\dagger}=1$ to finitely many local slots. Neither expansion is copied here. Theorem [2](#thm:sep){reference-type="ref" reference="thm:sep"} as a statement that $p$ comes from a pure process therefore depends on that external finite verification.

Nonnegativity of $L$ on three-bit process functions is an exhaustive check. The repository records $744$ such process functions, with $L\ge 0$ on each, the bound being tight on $418$ of them. This manuscript does not repeat the enumeration. A reader who does not grant it does not yet have, from this file alone, the proof that $p$ lies outside the convex hull. What this file proves unconditionally, given the tables, is the numerical value [\[eq:L\]](#eq:L){reference-type="eqref" reference="eq:L"}.

The separation is basis-dependent in a precise sense. Read in the computational basis, the induced distribution is the $p$ above. The same pure process, read in another frame, need not leave the convex hull of process functions. No claim is made that the board is a new quantum process in every frame, or that $L<0$ is a device-independent fact.

Finite tables of this size can be searched by enumerating output strings. That observation blocks any reading of Theorem [1](#thm:iff){reference-type="ref" reference="thm:iff"} or Theorem [2](#thm:sep){reference-type="ref" reference="thm:sep"} as a complexity separation or a hypercomputational claim. The search decides membership for an explicit table. It does not implement the wiring as a physical computer, and it does not transfer a runtime bound to a family the search was not given.

# Relation to prior work {#sec:prior}

Baumeler and Wolf introduce process functions as the deterministic classical processes in which every choice of local functions has a unique fixed point [@baumeler2016]. Equation [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is the reversible encoding used for that class. Baumeler, Costa, Ralph, Wolf, and Zych discuss reversible realization of deterministic classical processes compatible with arbitrary local operations inside a process theory, and they leave a general quantization of that bijection as a further question relative to the theory [@baumeler2019]. Theorem [1](#thm:iff){reference-type="ref" reference="thm:iff"} answers a narrower question: for this one encoding, unitarity of every closed loop under local unitaries and matched finite ancillas is equivalent to the process-function condition. It does not classify every unitary dilation.

Araújo *et al.* define a pure process by unitarity of the loop under local unitaries [@araujo2017]. Theorem [1](#thm:iff){reference-type="ref" reference="thm:iff"} says which classical rules meet that definition for the canonical extension. It does not say that purity restores a mixture of process functions. Theorem [2](#thm:sep){reference-type="ref" reference="thm:sep"} is a counterexample in one basis, and only once the external nonnegativity check is granted. Oreshkov, Costa, and Brukner introduce the process-matrix framework in which these loops are written [@oreshkov2012]. The two-party classification, that valid classical processes are mixtures of causally ordered process functions, is not re-proved here. The witness uses three parties because that is where the cited separation lives.

No speedup, query complexity, or spacetime embedding is stated. Equation [\[eq:U\]](#eq:U){reference-type="eqref" reference="eq:U"} is not a physical realization. A negative value of $L$ in one basis is not a claim about the ontology of the process in every basis.

::: ruledtabular
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

  : Exponents $m_o(z)\in\{0,1,2,3\}$. Rows are output strings $o$. Columns are $z=000,\ldots,111$.
:::
:::

::: ruledtabular
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

  : Coefficients $g_{io}$ of $L$. Row $i$, column $o$, binary order.
:::
:::

# Data availability {#data-availability .unnumbered}

The witness exponents and the coefficients of $L$ are Tables [1](#tab:m){reference-type="ref" reference="tab:m"} and [2](#tab:g){reference-type="ref" reference="tab:g"}. The conditional distribution is defined by Eqs. [\[eq:Uo\]](#eq:Uo){reference-type="eqref" reference="eq:Uo"}--[\[eq:p\]](#eq:p){reference-type="eqref" reference="eq:p"}, and the value [\[eq:L\]](#eq:L){reference-type="eqref" reference="eq:L"} is the contraction of those equations with Table [2](#tab:g){reference-type="ref" reference="tab:g"}. No separate dataset was generated. The enumeration of three-bit process functions and the cyclotomic coefficient check are finite calculations stored in the public repository [@archive]. That repository has no dataset DOI. No experimental data were created.

::: acknowledgments
Grok Bot, a Cursor cloud agent, drafted and arranged the prose of this manuscript, including the wording of the proofs, beyond spelling checks. It also ran the exact finite contraction of Tables [1](#tab:m){reference-type="ref" reference="tab:m"} and [2](#tab:g){reference-type="ref" reference="tab:g"} that produces Eq. [\[eq:L\]](#eq:L){reference-type="eqref" reference="eq:L"}. The model version is not recorded, and none is invented. The author set the scope: the finite canonical equivalence, the known board, and no new device or complexity claim. Human verification of the manuscript is pending. The agent is not an author. Funding and competing interests have not been confirmed; absence of a conflict is not declared. This draft has not been submitted.
:::
