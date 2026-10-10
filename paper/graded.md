# Can every consistent time loop live in a reversible world?

*A gentle, graded version of "Every process function lifts to a unitary process"*

**Draft. Not refereed.** This is a slow, explanatory retelling of the technical note [paper/lift.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/paper/lift.md) (web version: [the technical note](https://drewarrowood.github.io/process-function-unitary-lift/)). The technical note is the source of truth. If anything here seems to say more than the note does, the note wins, and the mismatch is a mistake in this version.

## How to read this

The note proves one theorem, studies a harder question it cannot yet settle, and draws some philosophical lessons. This version takes the same path, but slowly. It begins with stories and no symbols at all. Then it brings in notation one piece at a time. Each time a new symbol appears, I try to say three things:

1. **What it stands for.** The plain meaning.
2. **Why this choice.** Why this piece of mathematics captures the idea, rather than some other piece.
3. **What it commits us to.** Every formalism takes sides on something. Choosing a symbol is often choosing a philosophy.

Claims are marked by status, following Section 9 of the note:

- **Proved** means there is a proof. In a few places it is also machine-checked.
- **Evidence** means computer experiments or partial results that point one way but do not prove it.
- **Open** means nobody knows yet.
- **Interpretation** means philosophy. It is a reading of the mathematics, not a result.

The final section is all interpretation. A summary box at the very end says what is proved, what is evidence, and what is open.

---

## Part I. Stories, with no symbols

### 1. The letter nobody wrote

A woman finds a letter in her attic. It contains the plans for a machine. She builds the machine, and it is a time machine. She goes back a few decades and leaves the letter in the attic, where she will find it.

Nothing in this story is contradictory. Every event has a cause, and every event fits with every other event. Yet something is off. Who designed the machine? The plans were copied from the letter, and the letter was copied from the plans. The information came from nowhere.

Philosophers call this a *bootstrap* (or "ontological paradox"). It is not a contradiction. The trouble is the opposite: the story is *underdetermined*. Physics and the past together do not tell us what the letter says. A letter with completely different plans would have been just as consistent. So would a blank letter, which she never acts on. The loop permits many histories and does nothing to choose between them.

### 2. The grandfather

The more famous story runs the other way. A man travels back and prevents his grandfather from meeting his grandmother. Then he is never born, so he never travels back, so the grandparents meet, so he is born, so he travels back...

Here the trouble is the reverse of the bootstrap. There is no consistent history at all. Every candidate history contradicts itself.

The two stories mark the two ways a time loop can fail:

- **Too many** consistent histories (the bootstrap: underdetermination).
- **Too few**, namely none (the grandfather: paradox).

Keep this pair in mind. The whole note turns on asking for *exactly one*.

### 3. Lewis and Novikov: consistency

David Lewis, in "The paradoxes of time travel" (1976), dealt with the grandfather by splitting the word "can". Can the traveller kill his grandfather? He *can*, relative to his own abilities, his gun, and the local facts. He *cannot*, relative to the whole past, which includes the fact that the grandfather survived. Something will stop him: a slip on a banana peel, a jammed gun. There is no contradiction in the world. There is only a contradiction in the wish.

Physicists reached a similar view. Around 1990, Friedman, Morris, Novikov, Thorne and others proposed what is now called the *Novikov self-consistency principle*: only self-consistent histories occur. Echeverria, Klinkhammer and Thorne then studied billiard balls fired through a wormhole time machine. They found starting conditions with one consistent continuation, conditions with two, and conditions for which none was apparent.

So consistency, by itself, has two gaps. It throws out the grandfather histories, but it does not pick among the bootstrap ones. And, as John Earman warned, a consistency condition stuck on after the laws of motion is not itself a law of motion. It tells you which films are allowed. It does not tell you how the film runs.

### 4. A better rule: exactly one history, whatever anyone does

Here is a stronger demand. Imagine several people, each in a closed laboratory. Each receives something from outside (a message, a reading, a ball) and sends something back out. Somewhere outside the labs, the world may route their outputs back into their own past inputs. That is the time loop.

Now demand this:

> **However each person chooses to behave, there is exactly one consistent history.**

This rules out the grandfather, because there is always at least one consistent history. It rules out the bootstrap, because there is never more than one. And it does both *without taking anybody's freedom away*. The people in the labs may adopt any strategy whatsoever: "if I receive a 0, send a 1", "always send 0", anything. The loop is not allowed to forbid an action. It may only settle how everything fits together once the actions are chosen.

The note calls a loop with this property a **process function**. The idea comes from Baumeler and Wolf, and the "you may still do anything you could do in an ordinary lab" clause is the *no-new-physics* principle of Baumeler, Costa, Ralph, Wolf and Zych.

Lewis would recognise the move. The local "can" is untouched: every strategy is available. The global facts adapt, and they always adapt in exactly one way.

### 5. A coin flip inside a loop

Now a stranger story, which will come back near the end.

Three people sit in a ring of labs. Each holds one bit, a 0 or a 1. Before anything happens, a fair coin is tossed out of everyone's sight.

- **Heads**, the loop is a *copier*: each person receives exactly the bit sent by the previous person in the ring.
- **Tails**, the loop is a *negator*: each person receives the *opposite* of the bit sent by the previous person.

Neither loop is consistent on its own. Suppose everyone simply passes on what they receive. In the copier world, "all 0" and "all 1" both work: two histories, a bootstrap. In the negator world, a bit flipped three times around the ring must equal its own opposite: no history, a grandfather.

But look at the pair. Whenever the copier has two consistent histories, the negator has none. Whenever the negator has two, the copier has none. When someone ignores their input and sends a fixed bit, each loop has exactly one. Averaged over the coin, the number of consistent histories is always exactly one. The probabilities always add up to exactly 1, whatever anyone does.

So this is a *consistent* loop in the probabilistic sense. Every strategy yields a well-defined probability distribution over what happens. But its randomness is strange. It is not the randomness of ignorance about which of several consistent loops we live in, since neither the copier nor the negator is a consistent loop. The chance seems to be woven into the loop itself.

This loop is called **E_ex1** in the literature (Baumeler and Wolf). It is the central example of the second half of the note.

### 6. Reversibility

One more idea before the question. A process is *reversible* if from the way things end up you could, in principle, reconstruct exactly how they began. Nothing is forgotten. The fundamental laws of physics, as currently understood, are reversible in this sense. When information seems lost, as when an egg breaks or a message is burned, it has in fact been scattered into the environment.

Many consistent loops are not reversible. In the most famous three-person loop (the "Lugano" loop, Section 14 below), two different sets of actions can lead to the same set of received messages. Looking only at what was received, you cannot tell which happened.

But we can make any loop reversible by adding two things:

- a **source**: a place at the beginning that sends things in but receives nothing, and
- a **sink**: a place at the end that receives a record but sends nothing on.

The source is like an unknown initial condition. The sink is like the rest of the universe, which keeps a record of what was done. Baumeler, Costa, Ralph, Wolf and Zych showed that every process function becomes a reversible bijection once a source and a sink are added.

### 7. The question

Now the question of the note can be put without symbols:

> **Can every consistent loop live inside a reversible world?**

More precisely: take a consistent classical loop, made reversible with a source and a sink. Now let the people in the labs act in fully *quantum* ways. They may put their bits into superpositions, apply operations that have no classical counterpart, and entangle their labs with private equipment. Does the whole arrangement still behave sensibly, with probabilities that always add up to exactly one? Or does quantum freedom bring paradoxes back?

The note's first answer, the **main theorem**, is: yes, for every process function. The second question, which is **open**, is about loops with chance in them, like the coin-flip loop. Can they be realised reversibly? The note proves that the coin-flip loop E_ex1 cannot be. It conjectures that the only chancy loops that can be are those whose chance is mere ignorance about which deterministic consistent loop obtains.

The rest of this document builds the symbols needed to say all that exactly.

---
## Part II. The first symbols: loops as functions

### 8. Parties, inputs and outputs

We have **parties** numbered k = 1, 2, …, n. Think of each party as a closed laboratory with a person inside. Party k has:

- a set Iₖ of possible **inputs**, the things it might receive, and
- a set Oₖ of possible **outputs**, the things it might send out.

In the small examples both sets are {0, 1}: one bit in, one bit out.

**Why this choice.** We describe agents only by what crosses the walls of their labs. What happens inside is the agent's own business. This is a deliberately thin picture of agency: a lab is a black box with one door in and one door out, each used once.

**What it commits us to.** Two things. First, *locality of agency*: each party acts only on what it receives. It cannot reach out and alter another lab directly. Second, *finiteness*: the sets are finite. The note's results are for finite alphabets. Continuous variables, which Baumeler and coauthors also study, are not covered (Appendix B of the note).

When we write a whole list of outputs, one per party, we write o = (o₁, …, oₙ). The set of all such lists is the product O₁ × … × Oₙ, written ∏ Oₖ. Likewise i = (i₁, …, iₙ) is a list of inputs.

### 9. The environment as a map w: outputs → inputs

Here is the central object. The world outside the labs is described by a function

    w : ∏ Oₖ → ∏ Iₖ

which takes the list of everything the parties sent out and returns the list of what each party receives. Its k-th component wₖ(o) is what party k receives when the parties' outputs are o.

**Why a map from outputs to inputs?** This direction is the heart of the formalism, so it deserves a slow explanation.

In ordinary physics we write the world as a map from earlier states to later states. Here we have deliberately *not* said which party is earlier. Perhaps A acts before B. Perhaps B before A. Perhaps, in a loop, each is in some sense before the other. So we cannot write "A's output causes B's input" as a fixed arrangement. Instead we take the agents' actions as the free variables. The world's job is then: *given everything the agents did, say what each of them saw.*

The map w is this answer. It does not mention time at all. A party's input may depend on its "future" outputs as easily as on its "past" ones. That is exactly what allows loops.

**What it commits us to.**

- *No global time order is assumed.* Order, if there is one, has to be read off from the shape of w (who depends on whom). It is not built in.
- *The environment is deterministic.* Given the outputs, the inputs are fixed. (Part VI relaxes this, allowing randomness.)
- *Agents are the source of variation.* Everything "free" lives in the outputs. The world responds; it does not choose. This matches the no-new-physics stance of Section 4.

Notice one more thing. The map w alone is not yet a history. It says what the parties *would* receive for each possible list of outputs. A history is a list of outputs together with the inputs that w assigns to it, and it is only *actual* if it also fits with what the parties do on receiving those inputs. That fit is the next idea.

### 10. Interventions: what the agents do

Each party follows a **local intervention**, also called a strategy:

    fₖ : Iₖ → Oₖ

"If I receive this, I send that." The list f = (f₁, …, fₙ) is a choice of strategy for everybody.

**Why a function from input to output?** It is the most general deterministic behaviour of a closed lab with one door in and one door out. Whatever goes on inside, from the outside it is a rule that turns what came in into what goes out. Randomised strategies come later. They turn out to be averages of deterministic ones.

**What it commits us to.** We will quantify over *all* such f. That universal quantifier *is* the formal expression of freedom. We are not allowed to say "the loop is fine, provided nobody adopts strategy so-and-so." That would be the loop forbidding an action, which is the move Section 4 refused. (Whether the agents are free in some deeper metaphysical sense is another matter. The note says explicitly that it does not settle this. See Section 54.)

### 11. Fixed points: consistent histories

Put the two together. The agents send o. The world turns o into inputs w(o). Each agent turns its input into an output, fₖ(wₖ(o)). For the story to hang together, these outputs must be the very outputs o we started with:

    oₖ = fₖ(wₖ(o))   for every party k.

A list o that satisfies this is a **fixed point** of the composite map o ↦ f(w(o)). It goes all the way round the loop and comes back unchanged.

**Why a fixed point is the right notion.** A fixed point is precisely a *consistent history*. Every event in it is explained by the others, and nothing contradicts anything. The grandfather story is a loop with no fixed point. The letter-nobody-wrote story is a loop with more than one.

### 12. Process functions: exactly one fixed point, for every intervention

**Definition (process function).** A map w is a *process function* if, for every choice of local interventions f = (f₁, …, fₙ), the map o ↦ f(w(o)) has **exactly one** fixed point.

Unpack the logical shape: *for every* f, *there exists exactly one* o.

- "For every f" is freedom: no strategy is forbidden.
- "At least one o" is **no paradox**: no grandfather.
- "At most one o" is **no underdetermination**: no letter that nobody wrote.

**What it commits us to.** The definition encodes Lewis's "can" in its first quantifier, Novikov's consistency in its second, and adds a demand Novikov's principle lacked: uniqueness. The world is never left to choose between equally consistent pasts. Given the agents' choices, the history is settled.

### 13. Worked example: two parties, two bits

Let Alice (A) and Bob (B) each send and receive one bit. Write a for Alice's output and b for Bob's.

**A process function.** Let w(a, b) = (0, a). Alice always receives 0. Bob receives whatever Alice sent. Pick any strategies f_A and f_B. Consistency demands a = f_A(0) and b = f_B(a). The first equation fixes a. The second then fixes b. Exactly one history, whatever they do. This is ordinary one-way communication, Alice before Bob.

**Not a process function.** Let w(a, b) = (b, a). Each receives what the other sent: a two-way loop.

- Suppose both use the identity strategy, "send what you receive". Then a = b is all we need, so (0, 0) and (1, 1) are both consistent. *Two histories: a bootstrap.*
- Suppose Alice flips and Bob copies: a = not b and b = a. No bit equals its own negation. *No history: a grandfather.*

The same loop produces both failures, depending on what the agents do. That is typical.

**A fact about two parties.** There are 4⁴ = 256 maps from two bits to two bits. Exactly 12 are process functions (the note's code/check.py confirms this by brute force), and all 12 are causally ordered. In each of them, at most one direction of influence is used. With two parties and bits, consistency forces a time order.

### 14. Worked example: three parties and the Lugano loop

With three parties, something new happens. The **Lugano process function** (found by Araújo and Feix, and studied by Baumeler and Wolf) is

    w(a, b, c) = ( (not b) and c,   (not c) and a,   (not a) and b ).

Alice's input depends on Bob's and Charlie's outputs. Bob's depends on Charlie's and Alice's. Charlie's depends on Alice's and Bob's. If you draw an arrow from each party to the parties whose input it influences, you get a cycle. There is no first party.

Yet every one of the 4³ = 64 deterministic strategy choices has exactly one fixed point. For instance:

- Everyone copies their input: the unique history is a = b = c = 0.
- Everyone negates their input: the unique history is a = b = c = 1.
- Alice negates and the others copy: the unique history is (a, b, c) = (1, 1, 0). Check: w(1, 1, 0) = (0, 1, 0). Alice receives 0 and sends not 0 = 1. Bob receives 1 and sends 1. Charlie receives 0 and sends 0. ✓

So Lugano is a genuine causal loop with no paradox and no bootstrap. It is the standard example of a loop that violates a *causal inequality*, a statistical test passed by every arrangement with a definite time order.

Note also that Lugano is two-to-one: its eight output lists go to only four input lists. Looking at the inputs alone, you cannot recover the outputs. Lugano is consistent but not reversible. Section 17 fixes this.

### 15. The key lemma: someone can tell any two histories apart

Here is the one combinatorial fact the main theorem needs. It deserves the most philosophical attention, because it is where consistency turns into something a quantum world can use.

**Lemma (exclusivity).** Let w be a process function. Let s and s′ be two different lists of outputs. Then there is some party k such that

- sₖ ≠ s′ₖ (party k sends different things in the two lists), *but*
- wₖ(s) = wₖ(s′) (party k receives the same thing in both).

**In words.** Take any two different global scenarios. Some agent receives the same input in both, yet acts differently. That agent's own behaviour tells the two scenarios apart, using no information the agent did not have.

**Proof, in words, then symbols.** Suppose not. Then for every party, *receiving the same input in s and s′ means sending the same output*. Now build a strategy for each party:

- if you receive wₖ(s), send sₖ;
- if you receive wₖ(s′), send s′ₖ;
- otherwise do anything.

This is a legitimate strategy. The only possible clash is if wₖ(s) = wₖ(s′), and then, by our supposition, sₖ = s′ₖ, so the two instructions agree. But with these strategies, s is a consistent history (each party receives wₖ(s) and sends sₖ) and so is s′. Two distinct fixed points for one intervention: a bootstrap. That contradicts w being a process function. ∎

**Worked check.** For w(a, b) = (0, a), take s = (0, 0) and s′ = (1, 0). They differ at Alice, and Alice receives 0 in both. Alice is the witness. For the swap w(a, b) = (b, a), take s = (0, 0) and s′ = (1, 1). Alice receives 0 in one and 1 in the other. So does Bob. Nobody receives the same thing while acting differently. The lemma fails, and the swap duly has a bootstrap.

**Where this comes from, and what it commits us to.** This is the forward direction of a recent theorem of Dourdent, Leitherer, Boghiu, Simonov, Kunjwal and Acín (2026). They show that a list of events comes from a process function exactly when it is complete and *pairwise exclusive*. The note connects this to a principle of Specker: if any two of several questions can be answered jointly, then all of them can. Philosophically, the lemma says that consistency is a constraint on *distinguishability by local agents*. Two global histories are never so alike that no agent placed identically in both could tell them apart by its own actions. The theorem will turn this into orthogonality. In quantum mechanics, orthogonal means perfectly distinguishable.

---
## Part III. Making the loop reversible

### 16. Bijections: the arithmetic of not forgetting

A function is a **bijection** if it is one-to-one and onto: every possible result comes from exactly one starting point. A bijection can be run backwards. From the result you recover the start. That is the mathematical form of "no information is lost".

Lugano is not a bijection, as Section 14 showed. Of the 256 two-bit two-party maps, twelve are process functions and none of them is its own input–output reverse (the note, Section 6). Consistency does not give reversibility for free on the original alphabet.

### 17. Source and sink

The fix, due to Baumeler, Costa, Ralph, Wolf and Zych, is to add two new regions.

- The **source** P is a region that only *sends*. It has no input. Its value e = (e₁, …, eₙ) holds one symbol for each party, drawn from that party's input alphabet, so P = ∏ Iₖ.
- The **sink** F is a region that only *receives*. It has no output. It records one symbol for each party, drawn from that party's output alphabet, so F = ∏ Oₖ.

**What they represent.** Metaphysically, the source is the *initial condition*: the part of the world that is simply given and depends on nothing the agents do. The sink is the *final record*: the rest of the universe, into which every action leaves a trace. Physicists' reversible laws always come with this pair, a state you start from and a state you end in. Adding them to the loop is asking what the loop looks like as part of a whole world with a beginning and an end, rather than as an isolated knot.

### 18. The permutation U

The reversible version of w is the map

    U(o, e) = ( w(o) + e,  o ).

Read it slot by slot. It takes the parties' outputs o and the source value e. It returns two things:

- the parties' **inputs**, w(o) + e: what the loop would deliver, shifted by the source;
- the **sink record**, o: a copy of what the parties did.

**Why the "+".** We label each input alphabet Iₖ by the numbers 0, 1, …, |Iₖ| − 1 and add modulo |Iₖ| (so for bits, + is exclusive-or: 1 + 1 = 0). In mathematical terms Iₖ is treated as the cyclic group ℤₙ, with n = |Iₖ|. All we need is that adding e can be *undone* by subtracting e. Any group would do; the cyclic one is simply the most convenient. The output alphabets Oₖ need no structure at all.

**Why this is reversible.** Given the result (i, o), recover the start: the outputs are o (the sink kept them), and the source value is e = i − w(o). Nothing is lost. So U is a bijection, and it is one *for every map w*, process function or not. The source shift and the sink copy have absorbed all the forgetfulness.

**What it commits us to.** The sink keeps a perfect copy of the outputs. This is the classical ancestor of a principle we will meet again. In a reversible world, whatever is done leaves a record somewhere. Lemma D.1 of the note (Section 47 below) shows that something like this is *forced* in any reversible realisation, not just this one.

### 19. Worked examples of U

**One party, constant loop.** With a single party, the only process functions are constant maps (a lone party's input cannot depend on its own output, or it could contradict itself). Take w = 0. Then U(o, e) = (e, o). The source feeds the party's input, and the party's output goes to the sink. This is just an ordinary lab between a past and a future. Nothing loops.

**Two parties, one-way.** Take w(a, b) = (0, a). Then

    U(a, b, e_A, e_B) = ( e_A,  a + e_B,  a, b ).

Alice receives the source bit e_A. Bob receives Alice's output, shifted by the source bit e_B. The sink records (a, b). This is a causal chain from the source to Alice, from Alice to Bob, and from both to the sink.

**Lugano.**

    U(a, b, c, e) = ( ((not b) and c) + e₁,  ((not c) and a) + e₂,  ((not a) and b) + e₃,   a, b, c ).

The two-to-one loop has become one-to-one.

### 20. Open versus closed

There is a subtlety worth stating clearly, because the whole note depends on it. U is a bijection of the *open* system: outputs and source in, inputs and sink out. But the parties are still inside the loop. They take their inputs and turn them into their outputs. When we plug the parties in, the loop *closes*, and what remains is a map from source to sink.

Closing the loop is where consistency matters. For the swap w(a, b) = (b, a), U is still a perfectly good bijection. Close the loop with both parties copying, and source value e = (0, 0) has two consistent continuations, while e = (1, 0) has none (Section 25 computes this). The open bijection says nothing about the closed loop. The note's slogan: **U is a bijection for every w; closing the loop is well behaved exactly when w is consistent.** (The "only when" half of this is numerical evidence only, as Section 35 explains.)

---

## Part IV. Quantum vocabulary, one word at a time

### 21. Kets: |o⟩ as a perfectly distinguishable configuration

Quantum mechanics describes a system by a vector in a space of possibilities. The notation |o⟩, read "ket o", is the vector that stands for "the system is definitely in configuration o". Here o is one of our classical labels. The angle bracket marks it as a vector, not a number.

The kets for different labels are *orthogonal*: at right angles to one another. Orthogonal means *perfectly distinguishable*. There is a measurement that tells |0⟩ and |1⟩ apart with certainty.

What is new is that vectors can be added. For example,

    (1/√2)(|0⟩ + |1⟩)

is a legitimate state, a *superposition*. It is neither 0 nor 1, and it is not a coin flip between them either. The numbers in front (here 1/√2 each) are **amplitudes**. They can be negative or complex. When you finally look, the probability of each label is the squared magnitude of its amplitude: here ½ and ½.

**Why this notation.** The ket keeps the classical label in view while placing it inside a larger space. The classical world is not thrown away. It survives as a special basis, the "computational basis", of the quantum one.

**What it commits us to.** A wider space of possibilities than the classical one. Between "definitely 0" and "definitely 1" there are not just probabilities but superpositions with phases, and phases can *interfere*. Two routes to the same result may cancel. Any consistency condition that holds only for the classical labels might fail once we allow superpositions. That is the danger the note has to rule out.

We also write ⟨o| ("bra o") for the mirror image of |o⟩, and ⟨u|v⟩ for the inner product of two vectors. It is 1 when they are the same unit vector, 0 when they are orthogonal, and something in between otherwise.

### 22. Tensor products: independent agents

When two systems sit side by side, the space for both together is the **tensor product**, written ⊗. If Alice's bit lives in a two-dimensional space and Bob's in another, the pair lives in a 2 × 2 = 4-dimensional space with basis |0⟩⊗|0⟩, |0⟩⊗|1⟩, |1⟩⊗|0⟩, |1⟩⊗|1⟩. We usually write these as |00⟩, |01⟩, and so on.

When Alice acts with V_A on her system and Bob acts with V_B on his, the joint operation is V_A ⊗ V_B. It acts on each factor separately.

**Why this captures independence.** The tensor product is built so that local operations compose without interfering. Alice's action does not depend on which basis Bob uses, and the amplitude of a joint event is the product of the local amplitudes. Dimensions multiply, just as the number of joint classical configurations does.

**What it commits us to.** Each lab is a separate factor, and each agent acts only on its own factor. This is the quantum version of the locality of agency from Section 8. It also allows *entanglement*, joint states that are not products. The note's validity argument has to handle entangled equipment too (Section 34).

### 23. Unitaries: reversible, nothing lost

A **unitary** is a linear map U on a space of states that preserves every inner product. Equivalently,

    U U† = U† U = 1.

Here U† ("U dagger") is the conjugate transpose: flip the matrix across its diagonal and take complex conjugates. The 1 is the identity map, which does nothing.

**What this says.** U† undoes U. Every unitary is reversible, and its reverse is U†. Because inner products are preserved, perfectly distinguishable states stay perfectly distinguishable. Total probability is conserved: a normalised state stays normalised.

**Why unitary = reversible = no information lost.** These are three faces of one property. "Reversible": U† runs the process backwards. "No information lost": distinguishable inputs remain distinguishable outputs, since orthogonal stays orthogonal. "Probability conserved": lengths are preserved, so probabilities still sum to 1. In quantum theory the fundamental, closed-system dynamics is unitary. Anything else arises by ignoring part of a larger unitary story (Section 34).

**Classical bijections are unitaries.** A bijection of labels, extended to superpositions by linearity, is a *permutation matrix*. That is a matrix of 0s and 1s with exactly one 1 in each row and each column, and it is unitary. So U from Section 18 becomes the operator

    U |o⟩_O |e⟩_P = |w(o) + e⟩_I |o⟩_F.

The subscripts say which system each ket lives in: the parties' outputs O, the source P, the parties' inputs I, and the sink F. This is exactly the classical table, written in kets. It is the starting point of the note (Section 1 there).

**The Hadamard: a test with no classical analogue.** The Hadamard gate is

    H|0⟩ = (|0⟩ + |1⟩)/√2,   H|1⟩ = (|0⟩ − |1⟩)/√2.

It is unitary, but it is not a permutation. It turns definite bits into superpositions, with a minus sign that can cause cancellation. If a party inside the loop applies H, the loop sees something no classical strategy could produce. The note calls this "the test case". If U only behaved well for classical strategies, a Hadamard inside the loop is where it would break.

### 24. Ancillas: private equipment

A real laboratory has more than one bit's worth of equipment. We allow party k a private input system Xₖ and a private output system Yₖ (an **ancilla**, from the Latin for "servant"). The party's most general reversible action is then a unitary

    Vₖ : Iₖ ⊗ Xₖ → Oₖ ⊗ Yₖ,

which needs the dimensions to match: |Iₖ|·|Xₖ| = |Oₖ|·|Yₖ|. This also lets input and output alphabets have different sizes (Appendix B of the note).

**What it commits us to.** The agents are as powerful as quantum theory allows inside their labs. The theorem quantifies over *all* such Vₖ, with ancillas of any finite size. Again, the universal quantifier is the formal shape of freedom.

### 25. What "the lift works" means, and what failure looks like

Plug every party's Vₖ into U. Feed each input system Iₖ into Vₖ, and feed each output Oₖ back into U. What remains is a map from the source plus the parties' input ancillas to the sink plus their output ancillas:

    M : P ⊗ X → F ⊗ Y.

**The lift works** if M is unitary for every choice of local unitaries Vₖ. Araújo, Feix, Navascués and Brukner (2017, Definition 1) call such a process **pure**: unitaries in, unitary out.

**Why this is the right test.** If M were not unitary, some source state would come out with total probability more than 1 or less than 1. That would be a bootstrap or a grandfather appearing *in the quantum world*, even though the classical loop was fine.

**Failure, worked out.** Take the bad loop w(a, b) = (b, a), and let both parties do nothing (each Vₖ is the identity, "send what you receive"). The amplitude M[s, e], for sink record s given source value e, is 1 if s is consistent and 0 otherwise. Consistent means sₖ = wₖ(s) + eₖ for both parties. Notice that the source shift turns "do nothing" into the strategy "subtract eₖ". So each column of M counts the consistent histories of one classical intervention. Computed:

- e = (0, 0): s = (0, 0) and s = (1, 1) both work. The column has squared length 2.
- e = (1, 0): s_A = s_B + 1 and s_B = s_A. No solution. The column has length 0.
- e = (0, 1): length 0. e = (1, 1): length 2.

So M is not unitary. Probability is doubled for some source states and annihilated for others. The bootstrap and the grandfather reappear, as an excess and a deficit of probability.

For a process function and identity Vₖ, every column has exactly one 1, which is the classical definition again. The real question is what happens when the Vₖ are Hadamards, or arbitrary unitaries, so that many histories interfere.

---
## Part V. The main theorem, step by step

### 26. Statement

> **Theorem (proved).** Let w be a process function with finite alphabets. Let each party k apply any unitary Vₖ : Iₖ ⊗ Xₖ → Oₖ ⊗ Yₖ, with private ancillas of any finite size. Then the induced source-to-sink operator M : P ⊗ X → F ⊗ Y is unitary.

In plain words: **every consistent deterministic loop, made reversible with a source and a sink, stays reversible however quantum the agents inside it act.** Quantum freedom does not bring the paradoxes back.

### 27. The amplitude formula, read in words

The proof starts by writing down M explicitly. Its entries are

    M[(s, y), (e, x)] = ∏ₖ Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)].

Here is how to read this.

- **Left side.** The amplitude for the world to go from source value e and input ancillas x to sink record s and output ancillas y.
- **Right side.** The sink records s, and the sink holds the parties' outputs. So s *is* the list of what the parties sent. Given that, the loop delivers to party k the input wₖ(s), shifted by the source to wₖ(s) + eₖ. Party k then has to turn that input (with its ancilla xₖ) into its output sₖ (with ancilla yₖ). The amplitude for that is the matrix entry Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)].
- **The product ∏ₖ.** The parties act independently, so the joint amplitude is the product of the local amplitudes. This is the tensor product of Section 22 doing its job.

**Philosophical point.** Because the sink records the outputs, each entry of M corresponds to *a single* consistent assignment of inputs and outputs. There is no sum over alternative histories inside an entry. The sink's record has made the histories distinguishable, so they cannot interfere with each other on the way to the same final state. Whatever interference there is happens *between* entries, and that is what the next step controls.

### 28. The test: rows must be orthonormal

A square matrix is unitary when its rows are orthonormal. Each row must have length 1, and any two different rows must be orthogonal. In symbols, M M† = 1, which written out is

    (M M†)[(s, y), (s′, y′)] = Σ over e, x of M[(s, y), (e, x)] · conj M[(s′, y′), (e, x)].

We need this to be 1 when (s, y) = (s′, y′) and 0 otherwise.

**Meaning.** The rows are labelled by final records. So the test asks whether *different final records are perfectly distinguishable*, and whether each one carries total weight 1. Reversibility, in this form, is a statement about the records the world keeps.

### 29. Step 1: the sum splits into one factor per party

Plug the product formula into the sum. The sum is over all source values e = (e₁, …, eₙ) and all ancillas x = (x₁, …, xₙ). Each party's factor involves only that party's own eₖ and xₖ. A sum of products of independent pieces is a product of sums:

    (M M†)[(s, y), (s′, y′)] = ∏ₖ ( Σ over eₖ, xₖ of Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)] · conj Vₖ[(s′ₖ, y′ₖ), (wₖ(s′) + eₖ, xₖ)] ).

**Meaning.** The global question breaks into one local question per lab. This is where the source does its real work. Because each party has its own independent source symbol eₖ, summing over it lets each lab's input range over everything.

### 30. Step 2: a party that receives the same input contributes a clean 0 or 1

Look at party k's factor when wₖ(s) = wₖ(s′). Then both Vₖ entries have the *same* input slot, wₖ(s) + eₖ. As eₖ runs through all of Iₖ, so does that slot. Rename it i. The factor becomes

    Σ over i, xₖ of Vₖ[(sₖ, yₖ), (i, xₖ)] · conj Vₖ[(s′ₖ, y′ₖ), (i, xₖ)],

which is just the inner product of two rows of Vₖ. Since Vₖ is unitary, it is 1 if (sₖ, yₖ) = (s′ₖ, y′ₖ) and 0 otherwise.

**Meaning.** For a party in the same situation in both scenarios, local reversibility settles the question. Its factor is 1 if it did the same thing in both, and 0 if it acted differently.

### 31. Step 3: equal records give length 1

If s = s′, then wₖ(s) = wₖ(s′) for every k trivially, so every factor is of the kind in Step 2. The product is 1 exactly when y = y′. So every row has length 1, and rows with the same s but different ancilla records are orthogonal.

### 32. Step 4: different records give 0, thanks to the lemma

If s ≠ s′, the factors of parties with wₖ(s) ≠ wₖ(s′) could be anything. Here is where consistency enters. The exclusivity lemma (Section 15) guarantees a party k with wₖ(s) = wₖ(s′) and sₖ ≠ s′ₖ. That party's factor is of the Step 2 kind, and since sₖ ≠ s′ₖ, it is 0. One zero factor makes the whole product 0.

**Meaning.** Two different final records are orthogonal because some agent, placed identically in both scenarios, acted differently. Its local unitarity forces the zero. Without a process function, there may be no such witness, and the other factors can conspire to make M M† ≠ 1. The swap of Section 25 shows them doing it.

### 33. Step 5: square, hence unitary

So M M† = 1. M is also square: the source-plus-input-ancilla side has dimension ∏ |Iₖ||Xₖ|, and the sink-plus-output-ancilla side has dimension ∏ |Oₖ||Yₖ|, which are equal because each |Iₖ||Xₖ| = |Oₖ||Yₖ|. For square matrices, M M† = 1 implies M† M = 1. So M is unitary. ∎

**The whole proof in one sentence.** Each final record picks out a single consistent history (the sink), each lab contributes independently (the tensor product), a lab in the same situation in two histories contributes a clean 0 or 1 (local unitarity), and consistency guarantees that any two different histories have such a lab that acted differently (exclusivity).

**What is machine-checked.** The exclusivity lemma and the identities M M† = 1 and M† M = 1 are formally verified in the Lean 4 proof assistant with Mathlib. They are stated for complex amplitudes, any finite number of parties, any finite alphabets, and any finite local ancillas, with input and output sizes allowed to differ. The note names the theorems PFUL.induced_mul_conjTranspose, PFUL.induced_conjTranspose_mul and PFUL.induced_unitary (the last stating membership in the unitary group). They depend only on Lean's standard axioms. The lemma is *derived* in Lean, not assumed. Details are in [lean/STATUS.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/lean/STATUS.md).

### 34. From "unitary under unitaries" to "valid under everything"

Agents in labs do not only apply unitaries. They measure, add noise, discard things, and use equipment entangled with other labs. Does the result survive all that? The note's Appendix A shows that it does, by a standard argument (**proved on paper; not formalised in Lean**).

The key tool is **Stinespring dilation**. Any physically allowed operation, any "CPTP map" in the jargon (completely positive and trace preserving), can be written as three steps: add a fresh ancilla in a fixed state, apply a unitary to everything, then throw part of the result away. The throwing away is a *partial trace*: we average over what we can no longer see.

**Philosophical gloss.** Every noisy or irreversible operation is a reversible one *seen partially*. Irreversibility is ignorance of a larger story in which nothing is lost. This is the first appearance of the idea of **purification**, which drives the second half of the note.

With Stinespring in hand, the argument goes in four steps.

1. Local unitaries give a unitary M (the theorem).
2. A general local operation is a unitary on a larger lab followed by discarding. The extra systems never touch U, so the induced map is "append a state, apply the unitary M, discard". Each of those is physically allowed, so the composite is too.
3. Shared or entangled equipment is covered by *complete* positivity, which is exactly the property that an operation stays allowed when it acts on part of an entangled whole.
4. Measurements with outcomes ("instruments") give non-negative probabilities that add up to 1, by linearity.

Fix the source in |0⟩ and discard the sink, and you get back the classical loop w: each output o yields input w(o) with certainty. So the quantum lift contains the original classical loop as a special case.

### 35. The converse: evidence only

What if w is *not* a process function? Then the exclusivity property fails (Dourdent et al.). The note does *not* prove that unitarity must then fail in general. But numerically, every non-process function in the two- and three-party binary cases fails unitarity for random local unitaries (code/check.py). That fits the slogan of Section 20, but the "only if" direction is **evidence**, not proof.

The code also checks the theorem by brute force: all 12 two-party and 744 three-party binary process functions, under random local unitaries, with and without ancillas, plus three-symbol two-party examples. The deviation from unitarity stays below 10⁻¹³.

**What has been shown, philosophically.** Daher Ahmed and Kunjwal (2026) had conjectured this result and proved it for a subclass. They noted that the bare permutation unitary might fail to be a valid process. The note argues that it never fails. Araújo et al. (2017) had already written down this construction for Lugano, and Baumeler, Gilani and Rashid (2022) had remarked on unitary extensibility without a separate proof. The note's contribution is a short general proof for the coherent permutation unitary. Its philosophical reading is that **classical fixed-point consistency is already a quantization condition**. No extra quantum filter is needed.

---
## Part VI. Chance in loops: mixtures and purification

### 36. Classical processes: p(i | o)

Now let the environment be random. Instead of a function w, we have conditional probabilities

    p(i | o) = the probability that the parties receive the inputs i, given that they send the outputs o.

The "|" here is the ordinary probability bar, read "given". It is not part of a ket.

A **classical process** is such a p that is **logically consistent**. For every choice of local interventions, the total probability of all consistent histories must be exactly 1. (The full definition also covers randomised interventions, but deterministic ones are the heart of it.) For a deterministic p, which is just a w, this is the process-function condition again. Exactly one consistent history, with probability 1.

**What it commits us to.** Chance is put in the *environment*, not in the agents. And consistency is demanded only "on average". A random loop may be inconsistent in some of its deterministic pieces, as long as the probabilities always add up correctly. The coin-flip loop of Section 5 was exactly this.

### 37. The polytope: a map of all consistent loops

Collect all the numbers p(i | o) into one long list. Each classical process is then a point in a high-dimensional space. Logical consistency is a set of linear equations and inequalities (probabilities are non-negative, and certain sums equal 1). A region cut out by finitely many linear conditions like that is a **polytope**, a many-dimensional cousin of a polygon or a cut gemstone. This one is the **Baumeler–Wolf polytope**.

Three features of a polytope carry philosophical meaning.

- **Points inside** can be written as *mixtures*, that is, weighted averages, of other points. A mixture with weights p_j is the situation "with probability p_j, we are in process number j". Mixing is the geometry of *ignorance*. You know the menu of possibilities, but not which one obtains.
- **Vertices** (corners) are the points that are *not* mixtures of any other points. A vertex is a "pure option". There is no way of reading it as ignorance over something more definite inside the polytope.
- **Facets** are the flat outer walls. Each one is a linear inequality ("this weighted sum of probabilities is at most that one"), and the polytope is exactly the set of points satisfying all of them. Inequalities are how one *tests* membership. A facet violation is a certificate that a point is outside.

Every process function is a vertex: a deterministic point cannot be a mixture of other points. The question is whether there are other vertices.

- **Two binary parties.** The polytope has 12 vertices, and all of them are deterministic. They are the 12 process functions. Every two-party binary classical process is a mixture of process functions, so all its chance is ignorance about which deterministic consistent loop obtains.
- **Three binary parties.** The polytope has 710,760 vertices. Only 744 of them are deterministic, that is, process functions. All the rest are *random corners*: genuinely chancy consistent loops that are not mixtures of anything else (Baumeler and Wolf 2016).

Inside the big polytope sits a smaller one, the **process-function hull**, conv(PF). It is the set of all mixtures of the 744 process functions. For three binary parties, the random corners stick out beyond it.

### 38. Purification: randomness as ignorance of a hidden pure state

Can a chancy loop be realised in a reversible quantum world? The precise notion is **purifiability** (Araújo, Feix, Navascués and Brukner 2017, Definition 3).

A classical process W is *purifiable* if there is

- a unitary V, with a source and a sink, that is **pure**: unitary to unitary for every choice of local unitaries, as in Section 25; and
- a fixed **source state** |ψ⟩ (ψ is Greek "psi"),

such that preparing the source in |ψ⟩ and discarding the sink gives back exactly the probabilities of W.

**Why the word "purification".** In quantum theory a "pure" state is one of maximal knowledge, a single vector. A "mixed" state expresses uncertainty. Every mixed state can be seen as part of a larger pure state, with the uncertainty arising from not looking at the rest. To *purify* a random process is to exhibit it as a fragment of a deterministic, reversible, pure whole, with the randomness coming entirely from our lack of access to the source and the sink.

**What it commits us to.** That chance can be *explained away* as ignorance about a hidden but perfectly definite state of the world, as long as the world, once fully described, is reversible. Purifiability asks whether a given chancy loop admits such an explanation.

(The W here is the process written as a matrix, the "process matrix". For classical processes it is diagonal, with the numbers p(i | o) on the diagonal. Nothing below needs more than that.)

### 39. Mixtures of process functions are purifiable (proved)

**Proposition (proved; note, C.1).** Every mixture of process functions is purifiable.

**Construction, in words.** Suppose W is "process function w_j with probability p_j". Add to the source a *label register* that says which j. Build one big unitary that reads the label and runs the lift of w_j:

    U |o, e, j⟩ = |w_j(o) + e⟩_I  |o, j⟩_F.

Under local unitaries this acts as M_j on the j-th block, and each M_j is unitary by the main theorem. So the whole thing is pure. Now prepare the label in the superposition

    Σ_j √p_j |j⟩.

**Why the square roots.** Probabilities are squared amplitudes, so amplitude √p_j gives probability p_j.

**Why the sink must keep a copy of j.** If the sink records which j, the different branches are perfectly distinguishable at the end. When we discard the sink, the cross terms between branches vanish, and what remains is exactly Σ p_j W_{w_j} = W. If the label were *not* handed to the sink, the branches would still interfere, and the result would no longer be the classical mixture.

**Meaning.** This is randomness as ignorance, in its purest form. There is a definite fact about which loop we are in. It sits coherently in the source, and its trace is kept in the sink. We just do not see it.

The same trick mixes *any* purifiable processes, so the purifiable classical processes form a convex set containing the whole process-function hull. In particular, every two-party binary classical process is purifiable.

### 40. The classical version settles itself (proved)

Before going quantum, ask the classical question. Call W **classically purifiable** if it is what you see, averaging over a random source value λ, of a classical reversible process. That is, a bijection that stays a bijection from source to sink under every deterministic local intervention.

**Proposition (proved, sketch; note D.6).** W is classically purifiable if and only if it is a mixture of process functions.

**Why.** Fix the source value λ. You get a deterministic loop w_λ. For the source-to-sink map to stay a bijection under every intervention, each intervention must have exactly one consistent run. With zero runs, that source value would have no image. With two, two runs would collide in the sink, by counting. So each w_λ is a process function, and W is the λ-average of them. The converse is the random-source construction of Section 39.

**Meaning.** In a *classical* reversible world, chance in a consistent loop is always ignorance about which deterministic consistent loop obtains. This is now a theorem.

So the big question narrows sharply:

> **Does quantum reversibility allow anything that classical reversibility does not, for classical loops?**

---

## Part VII. The random corners

### 41. E_ex1, formally

Recall the coin-flip loop of Section 5. Let C be the *circular identity*, in which each party receives the previous party's output:

    x₁ = a₃,   x₂ = a₁,   x₃ = a₂

(here x is an input and a an output). Let C̄ be its bitwise negation: each party receives the opposite of the previous party's output. Then

    E_ex1 = ½ C + ½ C̄.

**Facts (proved; note, Appendix C).**

- E_ex1 is logically consistent. Section 5 gave the idea: C's surplus histories match C̄'s missing ones.
- E_ex1 is a *vertex* of the three-party binary polytope (the active constraints have full rank, 64 of 64). So it is not a mixture of process functions, nor of anything else.

So E_ex1 is a consistent loop whose chance is not ignorance over consistent deterministic loops. It averages two *inconsistent* deterministic loops. In the geometry of the polytope it is a corner: there is nothing more definite inside the polytope for its chance to be ignorance about.

### 42. Why E_ex1 cannot be purified: isotropic subspaces, gently

**Proposition (proved, exact certificate; note C.2).** E_ex1 is not purifiable.

The proof uses an exact criterion due to Araújo et al. (their Theorem 4). Here is its shape, without the full machinery.

**Step A: turn the question into linear algebra.** A purification would supply a set of vectors, one for each "piece" of W. There are r of them, where r is the **rank** of W (for E_ex1, r = 16). Some constraints on these vectors are linear. They force the vectors to live in a certain subspace V_W, whose dimension the note computes exactly: 27 for E_ex1. Araújo et al. give a necessary condition: dim V_W ≥ r. Intuitively, there must be room for 16 independent vectors. Here 27 ≥ 16, so this test does not rule anything out.

**Step B: the quadratic constraints.** The remaining constraints are *quadratic*. Certain quadratic forms must vanish identically on the whole r-dimensional span of the vectors. A subspace on which a quadratic form vanishes identically is called **totally isotropic** for that form.

**A toy picture.** Take the form q(x, y) = x² − y² on the plane. It vanishes on the line x = y and on the line x = −y. But there is no *plane* on which it vanishes, since the only plane available is the whole space, and q(1, 0) = 1. One plus direction and one minus direction allow at most a one-dimensional isotropic subspace. In general, a form with P positive directions, N negative directions and Z zero directions has totally isotropic subspaces of dimension at most Z + min(P, N). Each "null" direction has to pair a plus with a minus, and the zeros come for free.

**Step C: the certificate.** The note exhibits one explicit integer combination of the constraint forms. Its symmetric part, on the 27-dimensional space V_W, has exactly 13 positive directions, 13 negative and 1 zero. This was computed in exact rational arithmetic. So any totally isotropic subspace has dimension at most 1 + min(13, 13) = 14. But a purification needs a 16-dimensional one. Since 14 < 16, no purification exists. ∎

**What isotropy encodes, philosophically.** The linear conditions (Step A) say a purification has *enough room*. The quadratic conditions (Step B) say the room is *shaped right*. They ask that the hidden vectors fit together with no leftover interference: whatever cross terms appear between them must cancel. The certificate is a counting argument. There are not enough balanced plus/minus directions to host sixteen mutually cancelling directions. A coin flip inside a loop is too tightly wound to be unwound into a reversible whole.

**A numerical cross-check.** A gradient search for purifications drives the residual to about 10⁻¹³ for Lugano, which is purifiable, but stalls at 79.7 for E_ex1. The search agrees with the certificate.

### 43. The other random corners

Sampling 40,000 random vertices of the three-party binary polytope gave 646 non-deterministic ones. Up to symmetry (swapping parties and relabelling inputs and outputs) these fall into **51 orbits**. For all 51, the simple room test dim V_W ≥ rank W passes, so it decides nothing.

- **Proved (exact certificates):** orbits 7 and 50, the two orbits with dim V_W = 27. One of them contains E_ex1.
- **Evidence only:** for the other 49 orbits (dim V_W from 82 to 256), the certificate method was inconclusive. A GPU search, with 64 random restarts per orbit, found no purification for any of them. Best residuals ranged from 12.97 to 59.35, far from zero, while the same code finds Lugano's purification and stalls on E_ex1 as expected. A local search can miss solutions, so this is not a proof.

---
## Part VIII. The conjecture, and the evidence

### 44. The conjecture

> **Conjecture (open).** A classical process is purifiable if and only if it is a mixture of process functions.

The "if" direction is proved (Section 39). The "only if" direction is open. By Section 40, the conjecture is equivalent to:

> **A classical process that is quantum-purifiable is already classically purifiable.**

In words: for loops with classical statistics, quantum reversibility buys nothing that classical reversibility did not already give. If the conjecture holds, every reversible quantum realisation of a chancy classical loop is, at the level of its statistics, a coherent ignorance-mixture of deterministic consistent loops.

### 45. The hidden-label idea (Conjecture D.3)

The most natural strategy for proving the conjecture goes like this. Take any purification. Look inside its source. Hope to find a classical label λ, "which loop are we in?", such that for each value of λ the purification just runs one deterministic loop w_λ. Then W would be the λ-average of the w_λ. Each w_λ would have to be a process function, because the purification stays unitary on each label alone. And the conjecture would follow.

Stated precisely, the note's **Conjecture D.3** is: if V purifies a classical process, then there is an orthonormal basis {|λ⟩} of the source such that

    V |λ, o⟩ = (phase) · |w_λ(o)⟩ ⊗ |g_λ(o)⟩,

for functions w_λ (the loop for label λ) and g_λ, with g_λ one-to-one on outputs (the sink's record). The note shows that D.3 would imply the conjecture.

**What D.3 encodes.** It is a *hidden-variable* thesis. Underneath the quantum description there is a single classical fact, fixed in advance, about which deterministic loop is running. The fact is fixed independently of what the agents do.

### 46. The counterexample: contextual randomness (proved; note D.4)

**D.3 is false.** The counterexample is not even a time loop. It is an ordinary, causally ordered circuit.

**The story.** Alice has no input; she just chooses a bit oA. Then Bob receives a bit and sends one. The source holds two qubits, m and a, both starting in |0⟩. The circuit:

1. If oA = 1, apply a Hadamard to m. If oA = 0, leave m alone.
2. Copy m into a, using a controlled-NOT, which flips a exactly when m is 1.
3. Send m to Bob as his input.
4. Route oA, Bob's output oB, and a to the sink.

This is a circuit of unitaries in a fixed causal order, so it is a valid unitary process.

**What the parties see.**

- If oA = 0: m stays |0⟩, so Bob always receives 0.
- If oA = 1: m becomes (|0⟩ + |1⟩)/√2, the copy into a makes the branches distinguishable, and Bob receives 0 or 1 with probability ½ each.

**Is it a mixture of process functions? Yes.** Let λ be a fair coin and w_λ(oA) = λ·oA. With λ = 0, Bob always gets 0. With λ = 1, Bob gets Alice's bit. Average over λ: if oA = 0 Bob gets 0; if oA = 1, Bob gets 0 or 1 equally. That matches. The conjecture is not threatened.

**But there is no hidden label in the source.** Where, in the source, does the coin λ live? If Alice sends 0, the "coin" is read off the source in the ordinary 0/1 basis (the **Z basis**). If Alice sends 1, it is read off in the Hadamard-rotated basis (the **X basis**). These two bases are incompatible. Formally, for each input and output the note forms the operator

    G_{i,o} = V_o† (Π_i ⊗ 1_F) V_o

on the source. Here V_o is the purification with the parties' outputs fixed at o, and Π_i projects onto "the parties received i". This operator asks: "which source states lead to input i, given outputs o?" D.3 holds exactly when all the G's are projectors that commute with one another, since their common eigenbasis would be the label basis. Here the G's are Z-projectors when oA = 0 and X-projectors when oA = 1. They do not commute (commutator norm ½). So no single basis of the source works. Restricting attention to the actual source state |00⟩ does not help either.

**Philosophical meaning.** The randomness here *is* ignorance about which deterministic loop obtains, since W is a mixture. But the "which loop" variable is **contextual**. Which question the source answers depends on what Alice did. There is no fact sitting in the source, fixed in advance and independent of the agents' choices, that says "λ = 0" or "λ = 1". The ignorance reading survives as a claim about the *statistics* W. It fails as a claim about a single hidden label. (The resemblance to quantum contextuality in the Kochen–Specker sense is suggestive. That is an interpretive remark, not a result of the note.)

**Consequence for proofs.** No argument that tries to extract one classical label from the source can work. A proof of the conjecture must show *directly* that W lies in the process-function hull, for example by showing that purifiability implies every facet inequality of that hull.

### 47. Two things that cannot be the criterion

The note also proves two negative results. They say where the answer is *not*.

**Quantum-controlled interventions do not help (proved; note D.5).** One might hope that E_ex1 fails some weaker quantum test, such as letting the parties apply instruments coherently controlled by shared entangled equipment, and checking that probabilities still add to 1. They always do, for *every* classical process. Because W is classical (diagonal), it strips away all quantum coherence at the parties' doors. What remains is a classical joint behaviour that cannot be used to signal. Every such behaviour is an *affine* combination of local deterministic ones (signed weights allowed). The normalisation is linear and equals 1 on each deterministic strategy, so it equals 1 for all of them. So only the *unitarity* (reversibility) requirement can separate E_ex1 from mixtures. Consistency under quantum interventions is not enough.

**The actual source state is not enough (proved; notes D.2 and D.8).** Any test that looks only at what happens when the source is in its actual state |ψ⟩ is passed by every classical process, including E_ex1. This holds even when the parties use arbitrary local unitaries and superpositions of strategies. So any proof must use how the purification would act on source states *orthogonal* to |ψ⟩, the ones that never actually occur. In Araújo et al.'s terms, that is exactly the non-convex isotropic-subspace condition of Section 42.

**Philosophical gloss (interpretation).** What rules out E_ex1 is not anything that happens. It is the *modal* structure of the reversible world: how it would have behaved had it started differently. Reversibility is a constraint on counterfactuals, not only on actual histories.

A related structural fact (**proved; note D.1**): in any purification, the sink keeps a perfect record of the pair (outputs, inputs). The vectors it holds for different pairs are orthogonal, with squared lengths p(i | o). Reversibility forces a complete record, as Section 18 anticipated.

### 48. The facet evidence

If the conjecture is true, purifiability must imply every facet inequality of the process-function hull. So it helps to know those inequalities.

**Computed exactly (note D.7).** The 744 three-party binary process functions span a 37-dimensional space. Their hull has exactly **29,344 facets**, falling into **93 orbits** under the 384 symmetries (permuting parties and relabelling inputs and outputs). This was computed with the normaliz software on a rented 32-core machine in about 1.9 hours.

**One inequality separates everything sampled.** Facet orbit 82 contains the inequality

    p(000 | 000) ≤ p(000 | 001) + p(010 | 001) + p(000 | 100) + p(010 | 110) + p(011 | 111),

where each string lists the three parties' bits, inputs before the bar and outputs after it.

**Reading it.** The left side is the probability that, when everyone sends 0, everyone receives 0. The inequality says that this cannot be likely unless certain neighbouring events are at least as likely in total. For a deterministic process function it says: if w(000) = 000, then w(001) is 000 or 010, or w(100) = 000, or w(110) = 010, or w(111) = 011. It is a piece of combinatorial bookkeeping that every consistent deterministic loop obeys, and that mixtures therefore obey too. E_ex1 violates it: the left side is ½ and the right side is 0. Here is why. When everyone sends 0, the copier branch delivers 000, and that branch has probability ½. In each of the four situations on the right, neither the copier nor the negator delivers the listed inputs. For instance, when the outputs are 111 the copier delivers 111 and the negator 000, never 011.

Members of facet orbit 82 are violated by E_ex1 and by **all 51** sampled non-deterministic vertex orbits. So a single class of inequalities separates every sampled random corner from the hull. **Deriving it from purifiability is the natural next target. It has not been done.**

### 49. Walking from Lugano to E_ex1

The note also tests the boundary numerically (evidence; note D.8). Walk along the straight line from Lugano (purifiable) toward E_ex1 (not):

    x_t = (1 − t) · Lugano + t · E_ex1.

The process-function hull is left almost at once, at about t ≈ 2 × 10⁻⁷, because Lugano is a corner and this direction points straight out. The purification search finds nothing at t = 0.02 or t = 0.2, with best residuals 52.2 and 60.1. The same code reaches about 10⁻¹³ on Lugano itself. So along this line, purifiability appears to stop exactly where the hull does. That is consistent with the conjecture, but it is not proof.

### 50. Why the rest is hard

Three things make the open half of the conjecture difficult.

1. **The constraint is non-convex.** Whether a 16-dimensional (or larger) subspace exists on which many quadratic forms all vanish is not a convex question. Convex questions can usually be settled by duality: when no solution exists, there is a checkable certificate saying so. Non-convex questions offer no such guarantee. Single-form counting (Section 42) worked for the two smallest orbits. For the larger ones, single-form inertia, block forms and SDP relaxations (a standard convex approximation) have all stalled.
2. **The easy information is useless.** By D.2, D.5 and D.8, everything that can be read off from the actual source state is satisfied by every classical process. The proof must engage the unrealised source states, and that is exactly where the non-convexity lives.
3. **No hidden label.** By D.4, one cannot reduce the problem to finding a classical "which loop" variable. The argument has to work at the level of W itself, presumably facet by facet.

So the conjecture is open. D.3 is refuted. No counterexample to the conjecture itself has been found. That last point is weak evidence, because the large cases are untested.

---
## Part IX. Philosophical discussion

> **Everything in this part is interpretation.** It is a reading of the results above, following the note's own philosophical sections (3–8 and the end of 9). None of it is a theorem. Where a claim goes beyond the note's own wording, I say so.

### 51. Consistency is already a quantization condition

The classical demand "exactly one consistent history, whatever anyone does" was invented to dissolve the grandfather and the bootstrap. Nothing in it mentions amplitudes, phases or interference. Yet the main theorem shows that it is exactly strong enough to keep the quantum lift unitary. The proof makes the reason visible. Consistency guarantees that any two global histories are told apart by some agent who was in the same situation in both. Quantum mechanics turns "told apart by a local agent" into "orthogonal", and orthogonality is all unitarity needs.

So the note reads the result as saying that **fixed-point consistency is already a quantization condition**. The note surveys other quantum treatments of time loops. Deutsch's fixed-point model pays for its consistency with nonlinearity. Post-selection discards inconsistent branches, which the note calls a filter on samples, "of the same shape as a measure-zero axiom". Neither, the note argues, supplies the criterion. For process functions, the theorem shows that no extra quantum filter is needed. The classical consistency condition, imposed for all interventions, already carries over.

### 52. Can chance be fundamental inside a loop?

Two pictures of chance are in play.

- **Chance as ignorance.** The world is in a definite, deterministic state. Probabilities express what we do not know. In a loop, this means there is a definite consistent deterministic loop, and we are unsure which.
- **Chance as basic.** The world itself is chancy. No more definite story underlies the probabilities.

The polytope separates these pictures geometrically. Mixtures of process functions are ignorance. The random corners, such as E_ex1, are consistent loops whose chance cannot be read as ignorance over consistent deterministic loops.

The results so far:

- In a *classical* reversible world, only ignorance-chance is possible (D.6, proved).
- In a *quantum* reversible world, ignorance-chance is possible (C.1, proved), and at least some basic-chance loops are impossible (E_ex1, and every vertex in orbits 7 and 50, one of which contains E_ex1; proved).
- Whether *every* basic-chance loop is impossible in a quantum reversible world is the conjecture (open).

If the conjecture holds, the note's reading is this. Every reversible quantum loop with classical statistics is a coherent ignorance-mixture of deterministic consistent loops. Genuinely chancy loops like E_ex1 would be classically consistent but not reversibly realisable. **Reversibility, not consistency alone, would be the constraint that excludes basic chance from loops.** D.5 sharpens this: consistency under all quantum interventions holds for every classical process, so it is precisely the reversibility requirement that does the excluding.

### 53. Ignorance without a hidden label

The D.4 counterexample adds a caveat the note insists on. Even where chance *is* ignorance, the ignorance need not be about a single hidden label carried in the source. In D.4 the statistics are a mixture of deterministic loops. But "which loop" is answered differently depending on what Alice does. The ignorance reading is therefore a claim about the process W, not about any one hidden variable.

One might put it like this (this framing is mine, not the note's). The world may be "as if" one of several deterministic loops obtains, without there being a context-independent fact about which. That is a familiar pattern from the foundations of quantum mechanics. What is new here is only the setting.

### 54. Freedom, bilking and Lewis

Black's *bilking* argument against backward causation goes like this. If a later event causes an earlier one, an agent who sees the earlier event can act to prevent the later one. Either the agent cannot so act, which wants explaining, or the later event was not needed for the earlier one. Lewis answered that the agent can and cannot, in two senses of "can".

The process-function framework takes a definite side. It quantifies over *all* interventions, so no action is forbidden. The loop only constrains which global history results. The note is explicit that this does not settle whether the agent's choice was genuinely *open*. The fixed-point clause says the choice, if made, completes uniquely. Whether that answers Black depends on whether a consistency condition may rule out interventions, or only rule out histories given the interventions. The formalism is built for the view that consistency never forbids an intervention. As the note's Section 5 puts it, "Consistency is not allowed to forbid the operation. It is allowed only to constrain the global solution."

(A caution about wording. The note's Section 8 says it "takes the first reading", and the readings there are listed in the order "rule out interventions, or only rule out histories given the interventions". Read literally, that would be the opposite of its Section 5. I have followed Section 5 and the formalism, which quantifies over every intervention. The sentence in Section 8 of the technical note should be checked.)

### 55. Time symmetry and the reading of the source and sink

Read forwards, the source is an input and the sink is an output. Read backwards, using U†, they swap roles, and the reversed operator is the time-reversed process. In a loop like Lugano, an earlier input already depends on a later setting. Some authors, notably Price, argue that time symmetry pushes toward retrocausality. Leifer and Pusey made that argument precise under an assumption ("λ-mediation"), and Maudlin has objected to it. The note's position is modest. The mathematics does not choose between a retrocausal reading and a merely operational time-reverse. It does remove one cheap reply: one cannot say that the cyclic classical model dies as soon as the agents act quantumly.

### 56. What the theorem does not say

- **It is not about spacetime.** A unitary process on a finite alphabet is not a solution of Einstein's equations, and not a wormhole. The theorem says the event list has a unitary dilation. It does not say the dilation is a spacetime (see paper/EMBEDDING.md).
- **It does not classify all quantum processes.** It places every process function, including ones that violate causal inequalities, among the unitarily extendible processes. It says nothing about processes that are not deterministic classical functions, beyond the stochastic results of Parts VI–VIII.
- **It does not settle freedom** (Section 54).
- **The weak point is the lemma.** The combinatorial lemma is the piece an attacker has to break. Everything after it is row orthogonality. In this case the lemma is also machine-checked.

---

## What is proved, what is evidence, what is open

> **Proved**
>
> - Every process function, with any finite alphabets, lifts to a pure unitary process: under any local unitaries with any finite ancillas, the source-to-sink map is unitary. *Machine-checked in Lean 4 (exclusivity lemma; M M† = 1 and M† M = 1; unitary-group membership), standard axioms only.*
> - Validity under arbitrary local operations, entangled ancillas and instruments follows by Stinespring. *Standard paper argument, not formalised in Lean.*
> - Mixtures of process functions are purifiable (coherent random source, label recorded in the sink).
> - Classical reversible purifiability holds exactly for mixtures of process functions (D.6). So the conjecture says quantum reversibility adds nothing here.
> - E_ex1 and the vertex orbits 7 and 50 (one of which contains E_ex1) are not purifiable. *Exact rational certificates.*
> - In any purification, the sink holds an orthogonal record of (outputs, inputs) (D.1). Constraints on the fixed source state alone are vacuous (D.2). Validity under quantum-controlled interventions holds for every classical process (D.5).
> - The hidden-label strengthening D.3 is false. Counterexample: a causal circuit (D.4).
> - No certificate that uses only the fixed source state can rule out purification of any classical process (D.8).
> - The three-party binary process-function hull has exactly 29,344 facets in 93 orbits (exact computation with normaliz).
>
> **Evidence (not proof)**
>
> - A GPU search found no purification for any of the 49 remaining sampled non-deterministic vertex orbits. Best residuals 12.97–59.35.
> - A single facet orbit (82) is violated by E_ex1 and by all 51 sampled non-deterministic vertex orbits.
> - Along the segment from Lugano to E_ex1, purifiability appears to stop exactly where the hull does.
> - Numerically, non-process functions fail unitarity under random local unitaries (2- and 3-party binary). The converse of the main theorem is not proved.
>
> **Open**
>
> - The conjecture: a classical process is purifiable if and only if it is a mixture of process functions. The "if" half is proved. The "only if" half is open.
> - Deriving any facet inequality, for example orbit 82, from purifiability.
> - Any proof must use the purifying unitary on source states orthogonal to the actual one. That is the non-convex isotropy condition of Araújo et al.'s Theorem 4, where every certificate attempt so far has stalled for the larger orbits.
> - Spacetime embedding, continuous alphabets, and lifts built from bijections other than U are not addressed.

*For definitions, full proofs, references and code pointers, see the technical note, [paper/lift.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/paper/lift.md).*
