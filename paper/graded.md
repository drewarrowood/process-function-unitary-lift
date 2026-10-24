# Can every consistent time loop live in a reversible world?

*A gentle, graded version of "Every process function lifts to a unitary process"*

**Draft. Not refereed.** This is a slow, explanatory retelling of the technical note [paper/lift.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/paper/lift.md) (web version: [the technical note](https://drewarrowood.github.io/process-function-unitary-lift/)). The technical note is the source of truth. If anything here seems to say more than the note does, the note wins, and the mismatch is a mistake in this version.

## How to read this

The note has two results. First, every consistent deterministic loop (a process function) can be made quantum-reversible. Second, and this is now the note's main result, the natural guess that the *only* chancy loops that can be made quantum-reversible are mixtures of deterministic ones is **false** (Section 58h). It also draws some philosophical lessons. This version takes the same path, but slowly. It begins with stories and no symbols at all. Then it brings in notation one piece at a time. Each time a new symbol appears, I try to say three things:

1. **What it stands for.** The plain meaning.
2. **Why this choice.** Why this piece of mathematics captures the idea, rather than some other piece.
3. **What it commits us to.** Every formalism takes sides on something. Choosing a symbol is often choosing a philosophy.

**One thing this is not about: spacetime.** The stories below use time machines and wormholes as motivation, but the mathematics is about abstract loops between laboratories. A unitary process on a finite alphabet is not a solution of Einstein's equations, and not a wormhole. The theorem says that a consistent loop's list of events has a unitary dilation. It does not say that the dilation is a spacetime (see paper/EMBEDDING.md).

Claims are marked by status, following Section 9 of the note:

- **Proved** means there is a proof. In a few places it is also machine-checked.
- **Evidence** means computer experiments or partial results that point one way but do not prove it.
- **Open** means nobody knows yet.
- **Interpretation** means philosophy. It is a reading of the mathematics, not a result.

The path runs from easy to hard. Stories first (Part I). Then the symbols, one at a time (Parts II–IV). Then the main theorem and its proof (Part V), and why a machine-checked proof matters (Part VI). Then infinity, with Hilbert's hotel smuggled into a time loop (Part VII). The second half is about chance: mixtures and purification (Part VIII), the random corners that cannot be purified (Part IX), the conjecture, the evidence that seemed to support it, and the counterexample that refutes it (Part X, ending in Section 58h), and an honest map of the routes that failed (Part XI). Part XII is all philosophy, clearly marked as interpretation. A summary box at the very end says what is proved, what is evidence, and what is open.

---

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

Physicists reached a similar view. Around 1990, Friedman, Morris, Novikov, Thorne and others proposed what is now called the *Novikov self-consistency principle*: only self-consistent histories occur. Echeverria, Klinkhammer and Thorne (1991) then studied a billiard ball fired through a wormhole time machine. They chose "dangerous" starting conditions, where the ball would emerge in the past and knock its younger self off course: a billiard-table grandfather. One expects no consistent history. They found the opposite. A wide class of dangerous starts has *infinitely many* consistent continuations. Some quiet starts, such as a ball at rest far from the wormhole, have exactly one. They searched for a start with *no* consistent continuation and found none.

So the billiard balls illustrate the bootstrap, not the grandfather. The real trouble was too many histories, not too few.

So consistency, by itself, has two gaps. It throws out the grandfather histories, but it does not pick among the bootstrap ones, and the billiard balls show that the bootstrap is the live danger. And, as John Earman warned, a consistency condition stuck on after the laws of motion is not itself a law of motion. It tells you which films are allowed. It does not tell you how the film runs.

### 4. A better rule: exactly one history, whatever anyone does

Here is a stronger demand. Imagine several people, each in a closed laboratory. Each receives something from outside (a message, a reading, a ball) and sends something back out. Somewhere outside the labs, the world may route their outputs back into their own past inputs. That is the time loop.

Now demand this:

> **However each person chooses to behave, there is exactly one consistent history.**

Put plainly, "exactly one" rules out both failures at once. It rules out the grandfather (no consistent history), because there is always at least one. It rules out the bootstrap (more than one), because there is never more than one. Two old ideas have the same shape. Russell asked that a definite description such as "the author of the letter" denote exactly one thing, not none and not two. Newton's mechanics is prized because a well-posed initial-value problem has exactly one solution, given the starting conditions. And the demand does both *without taking anybody's freedom away*. The people in the labs may adopt any strategy whatsoever: "if I receive a 0, send a 1", "always send 0", anything. The loop is not allowed to forbid an action. It may only settle how everything fits together once the actions are chosen.

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

The note's first answer, the **main theorem**, is: yes, for every process function. The second question is about loops with chance in them, like the coin-flip loop. Can they be realised reversibly? The note proves that the coin-flip loop E_ex1 cannot be. It had conjectured that the only chancy loops that can be are those whose chance is mere ignorance about which deterministic consistent loop obtains. **That conjecture is false** (Section 58h). A machine with three labs and one bit each produces chancy statistics that are not any mixture of deterministic loops. This has been checked exactly, re-checked independently, and proved in a proof assistant, with two stated limits.

Two further questions ride along. What if the alphabets are infinite, so that a party can send any whole number? In a hotel with infinitely many rooms, a perfectly orderly shuffle can still leave a room empty, and we must check that a time loop cannot lose probability the same way (Part VII). And how sure can we be of a short proof about something this strange? Part VI tells the story of a referee who cannot be flattered.

The rest of this document builds the symbols needed to say all that exactly.

---

## Part II. The first symbols: loops as functions

### 8. Parties, inputs and outputs

We have **parties** numbered k = 1, 2, …, n. Think of each party as a closed laboratory with a person inside. Party k has:

- a set Iₖ of possible **inputs**, the things it might receive, and
- a set Oₖ of possible **outputs**, the things it might send out.

In the small examples both sets are {0, 1}: one bit in, one bit out.

**Why this choice.** We describe agents only by what crosses the walls of their labs. What happens inside is the agent's own business. This is a deliberately thin picture of agency: a lab is a black box with one door in and one door out, each used once.

**What it commits us to.** Two things. First, *locality of agency*: each party acts only on what it receives. It cannot reach out and alter another lab directly. Second, for now, *finiteness*: the sets are finite. Countably infinite alphabets are handled in Part VII. Continuous ones remain open.

A word about "agents" and "freedom", which recur throughout. Nothing in the mathematics models anyone *choosing*. As Section 10 explains, "freedom" will mean only the range of a quantifier: a condition must hold *for every* strategy a lab could follow.

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
- *The environment is deterministic.* Given the outputs, the inputs are fixed. (Part VIII relaxes this, allowing randomness.)
- *Agents are the source of variation.* Everything "free" lives in the outputs. The world responds; it does not choose. This matches the no-new-physics stance of Section 4.

Notice one more thing. The map w alone is not yet a history. It says what the parties *would* receive for each possible list of outputs. A history is a list of outputs together with the inputs that w assigns to it, and it is only *actual* if it also fits with what the parties do on receiving those inputs. That fit is the next idea.

### 10. Interventions: what the agents do

Each party follows a **local intervention**, also called a strategy:

    fₖ : Iₖ → Oₖ

"If I receive this, I send that." The list f = (f₁, …, fₙ) is a choice of strategy for everybody.

**Why a function from input to output?** It is the most general deterministic behaviour of a closed lab with one door in and one door out. Whatever goes on inside, from the outside it is a rule that turns what came in into what goes out. Randomised strategies come later. They turn out to be averages of deterministic ones.

**What it commits us to.** We will quantify over *all* such f. That universal quantifier *is* the formal expression of freedom, and it is all that "freedom" means here. Freedom is the range of the quantifier "for every f", not an act of anyone choosing. No agent, will or decision appears in the mathematics. There is only the demand that the conclusion hold whichever f is plugged in. We are not allowed to say "the loop is fine, provided nobody adopts strategy so-and-so." That would be the loop forbidding an action, which is the move Section 4 refused. (Whether the agents are free in some deeper metaphysical sense is another matter. The note says explicitly that it does not settle this. See Section 67.)

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

**What it commits us to.** The sink keeps a perfect copy of the outputs. This is the classical ancestor of a principle we will meet again. In a reversible world, whatever is done leaves a record somewhere. Lemma D.1 of the note (Section 56 below) shows that something like this is *forced* in any reversible realisation, not just this one.

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

Closing the loop is where consistency matters. For the swap w(a, b) = (b, a), U is still a perfectly good bijection. Close the loop with both parties copying, and source value e = (0, 0) has two consistent continuations, while e = (1, 0) has none (Section 26 computes this). The open bijection says nothing about the closed loop. The note's slogan: **U is a bijection for every w; closing the loop is well behaved exactly when w is consistent.** (The "only when" half of this is numerical evidence only, as Section 36 explains.)

### 21. A first look at the arrow of time

*A story.* A film shows a glass falling from a table and shattering. Run it backwards and you see shards leap from the floor and fuse into a glass on the table. Every frame of the reversed film obeys the laws of mechanics. We still know at once which way is "real".

Physicists usually explain the asymmetry by boundary conditions, not by the laws. The laws are reversible. The world happens to have started in a very special state, and records pile up toward the future. The glass leaves shards, sound waves and warmth, a sink full of traces. The source-and-sink picture of Section 17 has exactly this shape: a reversible U in the middle, a given starting state at one end, a record at the other.

**Interpretation (mine, not the note's).** In the lift, nothing irreversible happens inside U. Irreversibility appears only when we *fix* the source to one state and *discard* the sink, when we stop tracking the beginning and the end. Part VIII comes back to this. When a chancy loop can be realised reversibly at all, its randomness is the shadow of exactly that ignoring: a fixed source state and a discarded sink. Whether every chancy loop can be realised this way is the open question of Part X, and the coin-flip loop of Section 5 shows that some cannot.

---

## Part IV. Quantum vocabulary, one word at a time

### 22. Kets: |o⟩ as a perfectly distinguishable configuration

Quantum mechanics describes a system by a vector in a space of possibilities. The notation |o⟩, read "ket o", is the vector that stands for "the system is definitely in configuration o". Here o is one of our classical labels. The angle bracket marks it as a vector, not a number.

The kets for different labels are *orthogonal*: at right angles to one another. Orthogonal means *perfectly distinguishable*. There is a measurement that tells |0⟩ and |1⟩ apart with certainty.

What is new is that vectors can be added. For example,

    (1/√2)(|0⟩ + |1⟩)

is a legitimate state, a *superposition*. It is neither 0 nor 1, and it is not a coin flip between them either. The numbers in front (here 1/√2 each) are **amplitudes**. They can be negative or complex. When you finally look, the probability of each label is the squared magnitude of its amplitude: here ½ and ½.

**Why this notation.** The ket keeps the classical label in view while placing it inside a larger space. The classical world is not thrown away. It survives as a special basis, the "computational basis", of the quantum one.

**What it commits us to.** A wider space of possibilities than the classical one. Between "definitely 0" and "definitely 1" there are not just probabilities but superpositions with phases, and phases can *interfere*. Two routes to the same result may cancel. Any consistency condition that holds only for the classical labels might fail once we allow superpositions. That is the danger the note has to rule out.

We also write ⟨o| ("bra o") for the mirror image of |o⟩, and ⟨u|v⟩ for the inner product of two vectors. It is 1 when they are the same unit vector, 0 when they are orthogonal, and something in between otherwise.

### 23. Tensor products: independent agents

When two systems sit side by side, the space for both together is the **tensor product**, written ⊗. If Alice's bit lives in a two-dimensional space and Bob's in another, the pair lives in a 2 × 2 = 4-dimensional space with basis |0⟩⊗|0⟩, |0⟩⊗|1⟩, |1⟩⊗|0⟩, |1⟩⊗|1⟩. We usually write these as |00⟩, |01⟩, and so on.

When Alice acts with V_A on her system and Bob acts with V_B on his, the joint operation is V_A ⊗ V_B. It acts on each factor separately.

**Why this captures independence.** The tensor product is built so that local operations compose without interfering. Alice's action does not depend on which basis Bob uses, and the amplitude of a joint event is the product of the local amplitudes. Dimensions multiply, just as the number of joint classical configurations does.

**What it commits us to.** Each lab is a separate factor, and each agent acts only on its own factor. This is the quantum version of the locality of agency from Section 8. It also allows *entanglement*, joint states that are not products. The note's validity argument has to handle entangled equipment too (Section 35).

### 24. Unitaries: reversible, nothing lost

A **unitary** is a linear map U on a space of states that preserves every inner product. Equivalently,

    U U† = U† U = 1.

Here U† ("U dagger") is the conjugate transpose: flip the matrix across its diagonal and take complex conjugates. The 1 is the identity map, which does nothing.

**What this says.** U† undoes U. Every unitary is reversible, and its reverse is U†. Because inner products are preserved, perfectly distinguishable states stay perfectly distinguishable. Total probability is conserved: a normalised state stays normalised.

**Why unitary = reversible = no information lost.** These are three faces of one property. "Reversible": U† runs the process backwards. "No information lost": distinguishable inputs remain distinguishable outputs, since orthogonal stays orthogonal. "Probability conserved": lengths are preserved, so probabilities still sum to 1. In quantum theory the fundamental, closed-system dynamics is unitary. Anything else arises by ignoring part of a larger unitary story (Section 35).

**Classical bijections are unitaries.** A bijection of labels, extended to superpositions by linearity, is a *permutation matrix*. That is a matrix of 0s and 1s with exactly one 1 in each row and each column, and it is unitary. So U from Section 18 becomes the operator

    U |o⟩_O |e⟩_P = |w(o) + e⟩_I |o⟩_F.

The subscripts say which system each ket lives in: the parties' outputs O, the source P, the parties' inputs I, and the sink F. This is exactly the classical table, written in kets. It is the starting point of the note (Section 1 there).

**The Hadamard: a test with no classical analogue.** The Hadamard gate is

    H|0⟩ = (|0⟩ + |1⟩)/√2,   H|1⟩ = (|0⟩ − |1⟩)/√2.

It is unitary, but it is not a permutation. It turns definite bits into superpositions, with a minus sign that can cause cancellation. If a party inside the loop applies H, the loop sees something no classical strategy could produce. The note calls this "the test case". If U only behaved well for classical strategies, a Hadamard inside the loop is where it would break.

### 25. Ancillas: private equipment

A real laboratory has more than one bit's worth of equipment. We allow party k a private input system Xₖ and a private output system Yₖ (an **ancilla**, from the Latin for "servant"). The party's most general reversible action is then a unitary

    Vₖ : Iₖ ⊗ Xₖ → Oₖ ⊗ Yₖ,

which needs the dimensions to match: |Iₖ|·|Xₖ| = |Oₖ|·|Yₖ|. This also lets input and output alphabets have different sizes (Appendix B of the note).

**What it commits us to.** The agents are as powerful as quantum theory allows inside their labs. The theorem quantifies over *all* such Vₖ, with ancillas of any finite size. Again, the universal quantifier is the formal shape of freedom.

### 26. What "the lift works" means, and what failure looks like

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

### 27. Statement

> **Theorem (proved).** Let w be a process function with finite alphabets. Let each party k apply any unitary Vₖ : Iₖ ⊗ Xₖ → Oₖ ⊗ Yₖ, with private ancillas of any finite size. Then the induced source-to-sink operator M : P ⊗ X → F ⊗ Y is unitary.

In plain words: **every consistent deterministic loop, made reversible with a source and a sink, stays reversible however quantum the agents inside it act.** Quantum freedom does not bring the paradoxes back.

### 28. The amplitude formula, read in words

The proof starts by writing down M explicitly. Its entries are

    M[(s, y), (e, x)] = ∏ₖ Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)].

Here is how to read this.

- **Left side.** The amplitude for the world to go from source value e and input ancillas x to sink record s and output ancillas y.
- **Right side.** The sink records s, and the sink holds the parties' outputs. So s *is* the list of what the parties sent. Given that, the loop delivers to party k the input wₖ(s), shifted by the source to wₖ(s) + eₖ. Party k then has to turn that input (with its ancilla xₖ) into its output sₖ (with ancilla yₖ). The amplitude for that is the matrix entry Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)].
- **The product ∏ₖ.** The parties act independently, so the joint amplitude is the product of the local amplitudes. This is the tensor product of Section 23 doing its job.

**Philosophical point.** Because the sink records the outputs, each entry of M corresponds to *a single* consistent assignment of inputs and outputs. There is no sum over alternative histories inside an entry. The sink's record has made the histories distinguishable, so they cannot interfere with each other on the way to the same final state. Whatever interference there is happens *between* entries, and that is what the next step controls.

### 29. The test: rows must be orthonormal

A square matrix is unitary when its rows are orthonormal. Each row must have length 1, and any two different rows must be orthogonal. In symbols, M M† = 1, which written out is

    (M M†)[(s, y), (s′, y′)] = Σ over e, x of M[(s, y), (e, x)] · conj M[(s′, y′), (e, x)].

We need this to be 1 when (s, y) = (s′, y′) and 0 otherwise.

**Meaning.** The rows are labelled by final records. So the test asks whether *different final records are perfectly distinguishable*, and whether each one carries total weight 1. Reversibility, in this form, is a statement about the records the world keeps.

### 30. Step 1: the sum splits into one factor per party

Plug the product formula into the sum. The sum is over all source values e = (e₁, …, eₙ) and all ancillas x = (x₁, …, xₙ). Each party's factor involves only that party's own eₖ and xₖ. A sum of products of independent pieces is a product of sums:

    (M M†)[(s, y), (s′, y′)] = ∏ₖ ( Σ over eₖ, xₖ of Vₖ[(sₖ, yₖ), (wₖ(s) + eₖ, xₖ)] · conj Vₖ[(s′ₖ, y′ₖ), (wₖ(s′) + eₖ, xₖ)] ).

**Meaning.** The global question breaks into one local question per lab. This is where the source does its real work. Because each party has its own independent source symbol eₖ, summing over it lets each lab's input range over everything.

### 31. Step 2: a party that receives the same input contributes a clean 0 or 1

Look at party k's factor when wₖ(s) = wₖ(s′). Then both Vₖ entries have the *same* input slot, wₖ(s) + eₖ. As eₖ runs through all of Iₖ, so does that slot. Rename it i. The factor becomes

    Σ over i, xₖ of Vₖ[(sₖ, yₖ), (i, xₖ)] · conj Vₖ[(s′ₖ, y′ₖ), (i, xₖ)],

which is just the inner product of two rows of Vₖ. Since Vₖ is unitary, it is 1 if (sₖ, yₖ) = (s′ₖ, y′ₖ) and 0 otherwise.

**Meaning.** For a party in the same situation in both scenarios, local reversibility settles the question. Its factor is 1 if it did the same thing in both, and 0 if it acted differently.

### 32. Step 3: equal records give length 1

If s = s′, then wₖ(s) = wₖ(s′) for every k trivially, so every factor is of the kind in Step 2. The product is 1 exactly when y = y′. So every row has length 1, and rows with the same s but different ancilla records are orthogonal.

### 33. Step 4: different records give 0, thanks to the lemma

If s ≠ s′, the factors of parties with wₖ(s) ≠ wₖ(s′) could be anything. Here is where consistency enters. The exclusivity lemma (Section 15) guarantees a party k with wₖ(s) = wₖ(s′) and sₖ ≠ s′ₖ. That party's factor is of the Step 2 kind, and since sₖ ≠ s′ₖ, it is 0. One zero factor makes the whole product 0.

**Meaning.** Two different final records are orthogonal because some agent, placed identically in both scenarios, acted differently. Its local unitarity forces the zero. Without a process function, there may be no such witness, and the other factors can conspire to make M M† ≠ 1. The swap of Section 26 shows them doing it.

### 34. Step 5: square, hence unitary

So M M† = 1. M is also square: the source-plus-input-ancilla side has dimension ∏ |Iₖ||Xₖ|, and the sink-plus-output-ancilla side has dimension ∏ |Oₖ||Yₖ|, which are equal because each |Iₖ||Xₖ| = |Oₖ||Yₖ|. For square matrices, M M† = 1 implies M† M = 1. So M is unitary. ∎

**The whole proof in one sentence.** Each final record picks out a single consistent history (the sink), each lab contributes independently (the tensor product), a lab in the same situation in two histories contributes a clean 0 or 1 (local unitarity), and consistency guarantees that any two different histories have such a lab that acted differently (exclusivity).

**Checked by machine.** The lemma and both halves of unitarity are machine-checked in the Lean proof assistant, for complex amplitudes, any finite number of parties, any finite alphabets and any finite ancillas. Part VI explains what that means and why it matters.

**A warning for later.** Step 5 is the only step that uses counting: a *square* matrix with orthonormal rows is unitary. In infinite dimensions that step fails, and Part VII has to replace it with a different idea.

### 35. From "unitary under unitaries" to "valid under everything" (proved; machine-checked)

Agents in labs do not only apply unitaries. They measure, add noise, throw things away, and use equipment entangled with other labs. Does the result survive all that? The note's Appendix A shows that it does, and every step is now machine-checked in Lean (Part VI says why that matters).

The key tool is **Stinespring dilation**. Any physically allowed operation (a "CPTP map", in the jargon: completely positive and trace preserving) can be written in three steps. Add a fresh ancilla in a fixed state, apply a unitary to everything, then throw part of the result away. Throwing away is a *partial trace*: we average over what we can no longer see.

**Philosophical gloss.** Every noisy or irreversible operation is a reversible one *seen partially*. Irreversibility is ignorance of a larger story in which nothing is lost. This is the first appearance of the idea of **purification**, which drives the second half of this document.

With Stinespring in hand, the argument has four steps. Each comes with the Lean theorem that checks it.

1. **Local unitaries give a unitary M.** This is the theorem of Part V. Lean also proves the version where the local maps are isometries, not necessarily square (`PFUL.induced_isometry`). Packaged as a validity statement, `PFUL.valid` says the following. For any finite ancillas and any joint quantum state of the source and the labs' equipment, entangled or shared, both the global output and the state left in the sink are genuine density matrices: positive, with total probability 1.
2. **General local operations.** Any operation given by Kraus operators has an isometric Stinespring dilation that reproduces it (`PFUL.krausDilP_isometry`, `PFUL.ptrace_krausDil`). Validity for arbitrary local CPTP maps is `PFUL.valid_kraus`.
3. **Entangled and shared equipment.** This is already covered by step 1. The joint starting state is allowed to be anything.
4. **Measurements with outcomes (instruments).** Each outcome's conditional sink state is positive, and they add up to a density matrix, so outcome probabilities are non-negative and sum to 1 (`PFUL.valid_instrument`).

**The process-matrix form.** Physicists usually state validity differently, as a "generalised Born rule". Write the whole process as one matrix W = |U⟩⟩⟨⟨U|. Each lab's operation is likewise written as its *Choi matrix* C, a positive matrix that encodes the operation completely. The rule then asks that Tr[W(ρ ⊗ 1 ⊗ C₁ ⊗ … ⊗ Cₙ)] = 1 for every source state ρ and every allowed local operation. Lean checks this too:

- W is positive (`PFUL.Choi.procMat_posSemidef`).
- The Born-rule normalisation equals 1 for all local CPTP Choi matrices (`PFUL.Choi.bornC_eq_one`), and also with lab ancillas (`PFUL.Choi.bornC_anc_eq_one`, `PFUL.Choi.bornAnc_eq_one`). The last needs no structure at all on the ancilla types.
- The two ways of stating validity, the Born rule and "outputs are density matrices", are equivalent (`PFUL.Choi.afnb_iff_density`, and `PFUL.Choi.afnb_iff_density_split` in the exact layout of `PFUL.valid`).
- **Choi's theorem** itself is proved: an operation is completely positive exactly when its Choi matrix is positive (`PFUL.Choi.isCP_iff_choi`). So "completely positive" is a theorem about the matrices, not a definition slipped in by hand.
- One theorem bundles the whole chain: unitary validity, Kraus-channel validity and Born-rule normalisation for every completely positive, trace-preserving local operation (`PFUL.Choi.validity_package`).

Everything in this list is for finite dimensions, with standard axioms only. The one remaining technicality is the Choi form in *infinite* dimensions (Section 43).

Fix the source in |0⟩ and discard the sink, and you get back the classical loop w: each output o yields the input w(o) with certainty. The quantum lift contains the original classical loop as a special case.

### 36. The converse: evidence only

What if w is *not* a process function? Then the exclusivity property fails (Dourdent et al.). The note does *not* prove that unitarity must then fail in general. But numerically, every non-process function in the two- and three-party binary cases fails unitarity for random local unitaries (code/check.py). That fits the slogan of Section 20, but the "only if" direction is **evidence**, not proof.

The code also checks the theorem by brute force: all 12 two-party and 744 three-party binary process functions, under random local unitaries, with and without ancillas, plus three-symbol two-party examples. The deviation from unitarity stays below 10⁻¹³.

**What has been shown, philosophically.** Daher Ahmed and Kunjwal (2026) had conjectured this result and proved it for a subclass. They noted that the bare permutation unitary might fail to be a valid process. The note argues that it never fails. Araújo et al. (2017) had already written down this construction for Lugano, and Baumeler, Gilani and Rashid (2022) had remarked on unitary extensibility without a separate proof. The note's contribution is a short general proof for the coherent permutation unitary. Its philosophical reading, refined in Section 62, is that **consistency plus a complete record gives unitarity**. No extra quantum filter is needed.

---

## Part VI. The incorruptible referee: why machine-checked proof matters

### 37. A story: the referee who cannot be flattered

Imagine a referee with three odd traits. She reads every line, never skims, and never gets tired. She has no reputation to protect and no friends to please, so a famous name on the paper means nothing to her. And she accepts nothing she cannot rebuild from first principles. "It is well known that…" earns a polite refusal until you show her why.

Human refereeing has none of these traits reliably. Short proofs in mathematical physics often hide a step that "obviously" generalises: a square-matrix argument quietly reused in infinite dimensions, a sum swapped with a limit, an ancilla assumed to be unentangled. The proof in Part V is short. Part VII showed that one of its innocent-looking steps, "orthonormal rows plus square means unitary", is exactly the step that fails in Hilbert's hotel.

**Lean** is a proof assistant: a programming language in which definitions and proofs are written so precisely that a small, trusted program (the *kernel*) can check every inference. **Mathlib** is its large shared library of formalised mathematics. A theorem that compiles has been checked by the referee who cannot be flattered.

### 38. What exactly she has checked

These results are machine-checked, in Lean 4.34.1 with Mathlib, using only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no "sorry", meaning no unproved step, no custom axiom, and in the main results no `native_decide`, a shortcut that trusts the compiler.

- **The definition.** `PFUL.IsProcessFunction` w says that for every strategy f there is exactly one s with fₖ(wₖ(s)) = sₖ for all k. That is the definition of Section 12, transcribed.
- **The lemma is derived, not assumed.** `PFUL.exclusivity` proves Section 15 from the definition.
- **The main theorem.** M M† = 1 (`PFUL.induced_mul_conjTranspose`), M† M = 1 (`PFUL.induced_conjTranspose_mul`), and membership in the unitary group (`PFUL.induced_unitary`). These hold for complex amplitudes, any finite number of parties, any finite alphabets, and ancillas of any finite size, with input and output sizes allowed to differ. The row identity even holds over any field with a conjugation.
- **Validity under everything** (Section 35), including Choi's theorem, ending in `PFUL.Choi.validity_package`.
- **Countable alphabets** (Part VII), ending in `PFUL.Countable.induced_unitary_l2`.

### 39. What a referee cannot check

She checks that the proof proves the statement. She cannot check that the statement says what we *mean*. Two episodes from the repository's own history make the point.

- **The weaker theorem that looked like the real one.** Early Lean files proved row cancellation for integer-valued "rows". There, row orthonormality was a *hypothesis*, and so, in one file, was the witness party that the exclusivity lemma is supposed to supply. Those files compile. They are honestly labelled in lean/STATUS.md as "proved only under assumptions (NOT the paper's theorem)". A green tick on the wrong statement is still a green tick.
- **A claim marked as false on purpose.** The Lean files define a placeholder `SpacetimeEmbeddingClaim` and set it equal to False. This is a deliberate flag that nothing here says the loop is a spacetime (Section 70).

So machine-checking moves trust; it does not remove it. Trust moves away from the long chain of inferences and onto three short things: the small kernel, the three axioms, and the *definitions*. Anyone can read `PFUL.IsProcessFunction` in two lines and judge whether it captures "exactly one consistent history for every intervention". That is a much smaller thing to trust than a long chain of index-juggling.

**What remains unchecked.** The process-matrix (Choi) form Tr[W(…)] = 1 in infinite dimensions. The trace form of validity there is now checked (see below). Continuous alphabets, which have no settled definition yet. Everything in the stochastic half (Parts VIII–XI): the certificates there are exact computer arithmetic, but they are not Lean proofs. And, of course, every philosophical claim.

---

## Part VII. Infinity: Hilbert's hotel inside a time loop

### 40. A story: the hotel with infinitely many rooms

David Hilbert liked to describe a hotel with infinitely many rooms, numbered 1, 2, 3, and so on, all of them occupied. A new guest arrives. The manager asks every guest to move from room n to room n + 1. Nobody is turned out, nobody shares a room, and room 1 is now free. The move was perfectly one-to-one, and still a room appeared from nowhere. Run it the other way, everyone from n + 1 to n, and the guest in room 1 has nowhere to go.

Now smuggle the hotel into a time loop. Suppose a party's alphabet is infinite: it can receive and send any whole number. The source, the sink and the loop shuffle "guests" (basis states) between infinitely many "rooms". In a finite hotel, a shuffle that never doubles guests up must fill every room. That is the counting step at the end of the finite proof (Section 34: a square matrix with orthonormal rows is unitary). In an infinite hotel that step is simply false. The map could be like Hilbert's manager. Different sink records would stay perfectly distinguishable, but some state coming in from the source could fail to arrive anywhere in full. Probability would *leak* into the infinite corridors.

In quantum terms, the operator that moves n to n + 1 (the *shift*) has orthonormal rows but is not unitary. So the question for infinite alphabets is sharp. **Does the loop leak?**

### 41. The setting and the easy half (proved)

The note's Appendix F takes finitely many parties. Each input alphabet Iₖ is countable and carries a group structure, so the source can still "add" its value. The integers ℤ are the model case. Each output alphabet Oₖ is countable. Quantum states live in ℓ², the space of square-summable sequences over these sets: the infinite-dimensional analogue of the finite spaces we have used so far.

- **The open map is still a bijection (proved, F.1).** U|o, e⟩ = |w(o) + e, o⟩ shuffles basis states one-to-one and onto, with inverse (i, f) ↦ (f, i − w(f)). So U is unitary on ℓ². Here the hotel is harmless: U is a genuine bijection.
- **No interference between different histories (proved, F.2).** The exclusivity lemma holds for alphabets of any size. Its proof only ever prescribes two values of each strategy. Each matrix entry of M is still a single product with no infinite sum hiding inside it, so no question of convergence arises. The rows of M are orthonormal, M M† = 1, exactly as in Part V.

That is the half of unitarity that says *distinct records never blur together*. The other half, that *nothing leaks*, is where the hotel lurks.

### 42. The second half: count the consistent histories by chance (proved)

The finite proof got the second half for free by counting dimensions. The new proof (Appendix F.3) replaces counting with probability, and the idea is lovely.

**Step 1: read each lab as a random rule.** Fix a source value e (with ancilla x). Each party's unitary Vₖ turns an input into a superposition of outputs. The squared amplitudes give, for each input i, a probability distribution qₖ(· | i) over outputs. Because Vₖ is unitary, each of these really is a probability distribution, summing to 1.

**Step 2: draw a whole strategy at random.** For every party k and every possible input i, independently, draw an output fₖ(i) with probability qₖ(fₖ(i) | i). The result is a *random deterministic strategy* for everybody: a random choice of the f of Section 10. With infinitely many inputs this is an infinite product of probability spaces. That is perfectly standard measure theory.

**Step 3: notice what the column norm is.** The squared length of the column of M for source value e works out to

    Σ over o of ∏ₖ qₖ(oₖ | wₖ(o)).

The term for a given o is exactly the probability that o is a fixed point of the random strategy. Summing over all o, with Tonelli's theorem to justify swapping sum and expectation, gives the **expected number of fixed points**.

**Step 4: consistency finishes the job.** For a process function, *every* deterministic strategy has exactly one fixed point. So the number of fixed points is the constant 1, and its expectation is 1. Every column has length 1. Nothing leaks. Together with the orthonormal rows, M is unitary.

**Worked check.** For w(a, b) = (0, a), the column norm is Σ over a, b of q_A(a | 0) · q_B(b | a). Sum over b first: each q_B(· | a) sums to 1. Then sum over a: q_A(· | 0) sums to 1. Total 1, as promised. For the swap w(a, b) = (b, a) with both parties copying (q(o | i) = 1 exactly when o = i), the column norm is the number of a, b with a = b, which is 2. That is the bootstrap of Section 26 again: "probability" doubled.

**What the story shows.** Back in the hotel, a leak would be a source state with column length less than 1, a guest who checks in and never fully arrives. The expected-fixed-points argument shows that the guest is always *exactly* accounted for. The reason is the reason for everything else in this document. Every way the agents could behave yields exactly one consistent history. A random behaviour is just an average over such ways, and an average of ones is one.

**Philosophical gloss (interpretation).** Consistency does double duty. Through the exclusivity lemma it forbids different histories from interfering. Through the expected count it forbids probability from being created or destroyed. The first is a statement about *distinguishability*, the second about *conservation*. Both come from the single clause "exactly one fixed point, for every intervention."

The same argument also gives a second, *dimension-free* proof in the finite case. It never uses the fact that the matrix is square.

### 43. What the referee has checked about infinity

- **Finite alphabets, second proof (machine-checked).** The averaging identity `PFUL.Column.sum_prod_eq_one` holds over any commutative ring. Unit columns are `PFUL.induced_colnorm`. M† M = 1 from orthonormal rows plus unit columns, with no dimension count, is `PFUL.induced_conjTranspose_mul_of_colnorm`.
- **Countable alphabets (machine-checked).** The expected-fixed-points identity is `PFUL.Countable.tsum_prod_eq_one`, built with Mathlib's infinite product measure, and it allows inputs of any cardinality. Unit columns are `PFUL.Countable.induced_colnorm`. Orthonormal rows are `PFUL.Countable.induced_rows`, using the factorisation lemma `PFUL.Countable.hasSum_pi_prod`. The assembly is `PFUL.Countable.induced_unitary_l2`. It gives a linear isometric *equivalence* between the two ℓ² spaces whose matrix is M: a genuine unitary on infinite-dimensional Hilbert space. Its hypotheses are finitely many parties, countable alphabets and ancillas, and each Vₖ a unitary kernel. Standard axioms only.

**Still open or not formalised.**

- **Continuous alphabets (mostly settled, F.5).** Inputs in the real line or the circle. The closed loop is now defined for local operations that move points around (shifts, flips, squeezes, rearrangements, phase kicks), and for every local operation when the loop is causally ordered. In both cases it is proved unitary in the paper, for every loop, causal or not. The key lemma is machine-checked (`PFUL.Continuous`). The measure-theory step is now machine-checked too (Oct 23 2026): the loop map never squeezes or stretches volume, for any loop, causal or not (`PFUL.Continuous.tau_measurePreserving`, proved for the real line, the circle and any similar group). The loop built from shifts plus phase kicks is checked to be unitary (`closedLoop_unitary`). Still open: a canonical definition for non-causal loops with general local operations, such as a Fourier transform.
- **The process-matrix (Choi) form in infinite dimensions (formalised, small gaps).** The Born-rule pairing with W converges to 1 for countable alphabets, for any local channel given by Kraus operators or by a normal completely positive trace-preserving map (`valid_born_l2`, `valid_kraus_l2`, `valid_normalCPTP_l2`). The H.12 counterexample's own definitions are now tied to the general ones (`PFUL.Counterexample.isPF_iff`, `valid_of_mem_convexHull`). Left: purity of the counterexample with infinite-dimensional ancillas, and automatic continuity of positive trace-preserving maps (assumed as "normal").

---

## Part VIII. Chance in loops: mixtures and purification

### 44. Classical processes: p(i | o)

Now let the environment be random. Instead of a function w, we have conditional probabilities

    p(i | o) = the probability that the parties receive the inputs i, given that they send the outputs o.

The "|" here is the ordinary probability bar, read "given". It is not part of a ket.

A **classical process** is such a p that is **logically consistent**. For every choice of local interventions, the total probability of all consistent histories must be exactly 1. (The full definition also covers randomised interventions, but deterministic ones are the heart of it.) For a deterministic p, which is just a w, this is the process-function condition again. Exactly one consistent history, with probability 1.

**What it commits us to.** Chance is put in the *environment*, not in the agents. And consistency is demanded only "on average". A random loop may be inconsistent in some of its deterministic pieces, as long as the probabilities always add up correctly. The coin-flip loop of Section 5 was exactly this.

### 45. The polytope: a map of all consistent loops

Collect all the numbers p(i | o) into one long list. Each classical process is then a point in a high-dimensional space. Logical consistency is a set of linear equations and inequalities (probabilities are non-negative, and certain sums equal 1). A region cut out by finitely many linear conditions like that is a **polytope**, a many-dimensional cousin of a polygon or a cut gemstone. This one is the **Baumeler–Wolf polytope**.

Three features of a polytope carry philosophical meaning.

- **Points inside** can be written as *mixtures*, that is, weighted averages, of other points. A mixture with weights p_j is the situation "with probability p_j, we are in process number j". Mixing is the geometry of *ignorance*. You know the menu of possibilities, but not which one obtains.
- **Vertices** (corners) are the points that are *not* mixtures of any other points. A vertex is a "pure option". There is no way of reading it as ignorance over something more definite inside the polytope.
- **Facets** are the flat outer walls. Each one is a linear inequality ("this weighted sum of probabilities is at most that one"), and the polytope is exactly the set of points satisfying all of them. Inequalities are how one *tests* membership. A facet violation is a certificate that a point is outside.

Every process function is a vertex: a deterministic point cannot be a mixture of other points. The question is whether there are other vertices.

- **Two binary parties.** The polytope has 12 vertices, and all of them are deterministic. They are the 12 process functions. Every two-party binary classical process is a mixture of process functions, so all its chance is ignorance about which deterministic consistent loop obtains.
- **Three binary parties.** The polytope has 710,760 vertices. Only 744 of them are deterministic, that is, process functions. All the rest are *random corners*: genuinely chancy consistent loops that are not mixtures of anything else (Baumeler and Wolf 2016).

Inside the big polytope sits a smaller one, the **process-function hull**, conv(PF). It is the set of all mixtures of the 744 process functions. For three binary parties, the random corners stick out beyond it.

### 46. Purification: randomness as ignorance of a hidden pure state

Can a chancy loop be realised in a reversible quantum world? The precise notion is **purifiability** (Araújo, Feix, Navascués and Brukner 2017, Definition 3).

A classical process W is *purifiable* if there is

- a unitary V, with a source and a sink, that is **pure**: unitary to unitary for every choice of local unitaries, as in Section 26; and
- a fixed **source state** |ψ⟩ (ψ is Greek "psi"),

such that preparing the source in |ψ⟩ and discarding the sink gives back exactly the probabilities of W.

**Why the word "purification".** In quantum theory a "pure" state is one of maximal knowledge, a single vector. A "mixed" state expresses uncertainty. Every mixed state can be seen as part of a larger pure state, with the uncertainty arising from not looking at the rest. To *purify* a random process is to exhibit it as a fragment of a deterministic, reversible, pure whole, with the randomness coming entirely from our lack of access to the source and the sink.

**What it commits us to.** That chance can be *explained away* as ignorance about a hidden but perfectly definite state of the world, as long as the world, once fully described, is reversible. Purifiability asks whether a given chancy loop admits such an explanation.

(The W here is the process written as a matrix, the "process matrix". For classical processes it is diagonal, with the numbers p(i | o) on the diagonal. Nothing below needs more than that.)

### 47. Mixtures of process functions are purifiable (proved)

**Proposition (proved; note, C.1).** Every mixture of process functions is purifiable.

**Construction, in words.** Suppose W is "process function w_j with probability p_j". Add to the source a *label register* that says which j. Build one big unitary that reads the label and runs the lift of w_j:

    U |o, e, j⟩ = |w_j(o) + e⟩_I  |o, j⟩_F.

Under local unitaries this acts as M_j on the j-th block, and each M_j is unitary by the main theorem. So the whole thing is pure. Now prepare the label in the superposition

    Σ_j √p_j |j⟩.

**Why the square roots.** Probabilities are squared amplitudes, so amplitude √p_j gives probability p_j.

**Why the sink must keep a copy of j.** If the sink records which j, the different branches are perfectly distinguishable at the end. When we discard the sink, the cross terms between branches vanish, and what remains is exactly Σ p_j W_{w_j} = W. If the label were *not* handed to the sink, the branches would still interfere, and the result would no longer be the classical mixture.

**Meaning.** This is randomness as ignorance, in its purest form. There is a definite fact about which loop we are in. It sits coherently in the source, and its trace is kept in the sink. We just do not see it.

The same trick mixes *any* purifiable processes, so the purifiable classical processes form a convex set containing the whole process-function hull. In particular, every two-party binary classical process is purifiable.

### 48. The classical version settles itself (proved)

Before going quantum, ask the classical question. Call W **classically purifiable** if it is what you see, averaging over a random source value λ, of a classical reversible process. That is, a bijection that stays a bijection from source to sink under every deterministic local intervention.

**Proposition (proved, sketch; note D.6).** W is classically purifiable if and only if it is a mixture of process functions.

**Why.** Fix the source value λ. You get a deterministic loop w_λ. For the source-to-sink map to stay a bijection under every intervention, each intervention must have exactly one consistent run. With zero runs, that source value would have no image. With two, two runs would collide in the sink, by counting. So each w_λ is a process function, and W is the λ-average of them. The converse is the random-source construction of Section 47.

**Meaning.** In a *classical* reversible world, chance in a consistent loop is always ignorance about which deterministic consistent loop obtains. This is now a theorem.

So the big question narrows sharply:

> **Does quantum reversibility allow anything that classical reversibility does not, for classical loops?**

---

## Part IX. The random corners

### 49. E_ex1, formally

Recall the coin-flip loop of Section 5. Let C be the *circular identity*, in which each party receives the previous party's output:

    x₁ = a₃,   x₂ = a₁,   x₃ = a₂

(here x is an input and a an output). Let C̄ be its bitwise negation: each party receives the opposite of the previous party's output. Then

    E_ex1 = ½ C + ½ C̄.

**Facts (proved; note, Appendix C).**

- E_ex1 is logically consistent. Section 5 gave the idea: C's surplus histories match C̄'s missing ones.
- E_ex1 is a *vertex* of the three-party binary polytope (the active constraints have full rank, 64 of 64). So it is not a mixture of process functions, nor of anything else.

So E_ex1 is a consistent loop whose chance is not ignorance over consistent deterministic loops. It averages two *inconsistent* deterministic loops. In the geometry of the polytope it is a corner: there is nothing more definite inside the polytope for its chance to be ignorance about.

### 50. Why E_ex1 cannot be purified: isotropic subspaces, gently

**Proposition (proved, exact certificate; note C.2).** E_ex1 is not purifiable.

The proof uses an exact criterion due to Araújo et al. (their Theorem 4). Here is its shape, without the full machinery.

**Step A: turn the question into linear algebra.** A purification would supply a set of vectors, one for each "piece" of W. There are r of them, where r is the **rank** of W (for E_ex1, r = 16). Some constraints on these vectors are linear. They force the vectors to live in a certain subspace V_W, whose dimension the note computes exactly: 27 for E_ex1. Araújo et al. give a necessary condition: dim V_W ≥ r. Intuitively, there must be room for 16 independent vectors. Here 27 ≥ 16, so this test does not rule anything out.

**Step B: the quadratic constraints.** The remaining constraints are *quadratic*. Certain quadratic forms must vanish identically on the whole r-dimensional span of the vectors. A subspace on which a quadratic form vanishes identically is called **totally isotropic** for that form.

**A toy picture.** Take the form q(x, y) = x² − y² on the plane. It vanishes on the line x = y and on the line x = −y. But there is no *plane* on which it vanishes, since the only plane available is the whole space, and q(1, 0) = 1. One plus direction and one minus direction allow at most a one-dimensional isotropic subspace. In general, a form with P positive directions, N negative directions and Z zero directions has totally isotropic subspaces of dimension at most Z + min(P, N). Each "null" direction has to pair a plus with a minus, and the zeros come for free.

**Step C: the certificate.** The note exhibits one explicit integer combination of the constraint forms. Its symmetric part, on the 27-dimensional space V_W, has exactly 13 positive directions, 13 negative and 1 zero. This was computed in exact rational arithmetic. So any totally isotropic subspace has dimension at most 1 + min(13, 13) = 14. But a purification needs a 16-dimensional one. Since 14 < 16, no purification exists. ∎

**What isotropy encodes, philosophically.** The linear conditions (Step A) say a purification has *enough room*. The quadratic conditions (Step B) say the room is *shaped right*. They ask that the hidden vectors fit together with no leftover interference: whatever cross terms appear between them must cancel. The certificate is a counting argument. There are not enough balanced plus/minus directions to host sixteen mutually cancelling directions. A coin flip inside a loop is too tightly wound to be unwound into a reversible whole.

**A numerical cross-check.** A gradient search for purifications drives the residual to about 10⁻¹³ for Lugano, which is purifiable, but stalls at 79.7 for E_ex1. The search agrees with the certificate.

### 51. The other random corners

How were these corners found? Not by listing all 710,760 vertices of the three-party binary polytope. The note's code (code/stochastic/sample.py) solved 40,000 linear programs. Each one minimised a random linear objective, with independent Gaussian coefficients, over the Baumeler–Wolf polytope, that is, over all logically consistent p(i | o). Each optimum is a vertex. Of the 40,000 vertices found, 39,354 were deterministic (process functions) and only 646 were non-deterministic. Yet only 744 of the 710,760 vertices are deterministic. So the method is far from uniform: random objectives land on corners in proportion to how "pointy" they are, and the process functions are evidently very pointy. **The 51 orbits are therefore only as representative as this sampling.** Indeed most random corners have certainly never been seen. A symmetry orbit has at most 384 members, so the 51 orbits contain at most 51 × 384 = 19,584 vertices, under 3% of the 710,016 non-deterministic ones.

Up to symmetry (swapping parties and relabelling inputs and outputs), the 646 non-deterministic samples fall into **51 orbits**. For all 51, the simple room test dim V_W ≥ rank W passes, so it decides nothing.

- **Proved (exact certificates):** orbits 7 and 50, the two orbits with dim V_W = 27. One of them contains E_ex1.
- **Evidence only:** for the other 49 orbits (dim V_W from 82 to 256), the certificate method was inconclusive. A GPU search, with 64 random restarts per orbit, found no purification for any of them. Best residuals ranged from 12.97 to 59.35, far from zero, while the same code finds Lugano's purification and stalls on E_ex1 as expected. A local search can miss solutions, so this is not a proof.

---

## Part X. The conjecture, the evidence, and the refutation

### 52. The conjecture

> **Conjecture (now refuted; see Section 58h).** A classical process is purifiable if and only if it is a mixture of process functions.

The "if" direction is proved (Section 47). The "only if" direction is false (Section 58h). Sections 52–58g are kept as they were written, while it was open. By Section 48, the conjecture is equivalent to:

> **A classical process that is quantum-purifiable is already classically purifiable.**

In words: for loops with classical statistics, quantum reversibility buys nothing that classical reversibility did not already give. If the conjecture holds, every reversible quantum realisation of a chancy classical loop is, at the level of its statistics, a coherent ignorance-mixture of deterministic consistent loops.

### 53. A story: two workshops

Two workshops build time loops to order. The first, the *clockmaker's*, uses only classical parts: gears, levers, a shuffled deck sealed in a drawer at the start, and a ledger at the end that records everything. Its machines are reversible: from the ledger and the final positions you could reconstruct the deck. The second, the *quantum workshop*, may use anything quantum mechanics allows: superposed gears, entangled drawers, interference. Its machines must also be reversible, in the quantum sense.

A customer orders a loop with given classical statistics: "under every strategy, these inputs with these probabilities".

- The clockmaker can build exactly the **mixtures of process functions**. The shuffled deck picks a deterministic consistent loop, and the ledger remembers which (Section 48, proved).
- The quantum workshop can build at least those (Section 47, proved). It provably *cannot* build the coin-flip loop E_ex1 (Section 50, proved).

The conjecture said the two order books are identical (Section 58h shows they are not). **Quantum reversibility buys loops nothing that classical reversibility does not.** If true, all the extra power of the quantum workshop, its superpositions and interference, is invisible in the classical statistics of a loop. Whatever it builds, the clockmaker could have built with a shuffled deck.

### 54. The hidden-label idea (Conjecture D.3)

The most natural strategy for proving the conjecture goes like this. Take any purification. Look inside its source. Hope to find a classical label λ, "which loop are we in?", such that for each value of λ the purification just runs one deterministic loop w_λ. Then W would be the λ-average of the w_λ. Each w_λ would have to be a process function, because the purification stays unitary on each label alone. And the conjecture would follow.

Stated precisely, the note's **Conjecture D.3** is: if V purifies a classical process, then there is an orthonormal basis {|λ⟩} of the source such that

    V |λ, o⟩ = (phase) · |w_λ(o)⟩ ⊗ |g_λ(o)⟩,

for functions w_λ (the loop for label λ) and g_λ, with g_λ one-to-one on outputs (the sink's record). The note shows that D.3 would imply the conjecture.

**What D.3 encodes.** It is a *hidden-variable* thesis. Underneath the quantum description there is a single classical fact, fixed in advance, about which deterministic loop is running. The fact is fixed independently of what the agents do.

### 55. The counterexample: contextual randomness (proved; note D.4)

*A story first: the coin whose face is decided by how you look.* A sealed token sits in a drawer. Alice, in the first lab, makes a choice. Then Bob, in the second lab, receives a bit. The whole thing behaves exactly as if a fair coin had been tossed in advance. Heads, Bob's bit is a copy of Alice's. Tails, Bob always receives 0. Naturally you assume the coin's face is written somewhere in the drawer, waiting.

It is not. If Alice chooses 0, the token is consulted with one question, and the face does not matter, since both "loops" give Bob a 0. If Alice chooses 1, the token is consulted with a *different*, incompatible question, and only then does a face appear, at random. There is no single way of reading the token that would serve as the coin for both of Alice's choices. The statistics are those of a coin tossed in advance. The mechanism is a coin whose face is decided by how you look.

Now the details.

**D.3 is false.** The counterexample is not even a time loop. It is an ordinary, causally ordered circuit.

**The circuit.** Alice has no input; she just chooses a bit oA. Then Bob receives a bit and sends one. The source holds two qubits, m and a, both starting in |0⟩. The circuit:

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

### 56. Two things that cannot be the criterion

The note also proves two negative results. They say where the answer is *not*.

**Quantum-controlled interventions do not help (proved; note D.5).** One might hope that E_ex1 fails some weaker quantum test, such as letting the parties apply instruments coherently controlled by shared entangled equipment, and checking that probabilities still add to 1. They always do, for *every* classical process. Because W is classical (diagonal), it strips away all quantum coherence at the parties' doors. What remains is a classical joint behaviour that cannot be used to signal. Every such behaviour is an *affine* combination of local deterministic ones (signed weights allowed). The normalisation is linear and equals 1 on each deterministic strategy, so it equals 1 for all of them. So only the *unitarity* (reversibility) requirement can separate E_ex1 from mixtures. Consistency under quantum interventions is not enough.

**The actual source state is not enough (proved; notes D.2 and D.8).** Any test that looks only at what happens when the source is in its actual state |ψ⟩ is passed by every classical process, including E_ex1. This holds even when the parties use arbitrary local unitaries and superpositions of strategies. So any proof must use how the purification would act on source states *orthogonal* to |ψ⟩, the ones that never actually occur. In Araújo et al.'s terms, that is exactly the non-convex isotropic-subspace condition of Section 50.

**Philosophical gloss (interpretation).** What rules out E_ex1 is not anything that happens. It is the *modal* structure of the reversible world: how it would have behaved had it started differently. Reversibility is a constraint on counterfactuals, not only on actual histories.

A related structural fact (**proved; note D.1**): in any purification, the sink keeps a perfect record of the pair (outputs, inputs). The vectors it holds for different pairs are orthogonal, with squared lengths p(i | o). Reversibility forces a complete record, as Section 18 anticipated.

### 57. The facet evidence

If the conjecture is true, purifiability must imply every facet inequality of the process-function hull. So it helps to know those inequalities.

**Computed exactly (note D.7).** The 744 three-party binary process functions span a 37-dimensional space. Their hull has exactly **29,344 facets**, falling into **93 orbits** under the 384 symmetries (permuting parties and relabelling inputs and outputs). This was computed with the normaliz software on a rented 32-core machine in about 1.9 hours.

**One inequality separates everything sampled.** Facet orbit 82 contains the inequality

    p(000 | 000) ≤ p(000 | 001) + p(010 | 001) + p(000 | 100) + p(010 | 110) + p(011 | 111),

where each string lists the three parties' bits, inputs before the bar and outputs after it.

**Reading it.** The left side is the probability that, when everyone sends 0, everyone receives 0. The inequality says that this cannot be likely unless certain neighbouring events are at least as likely in total. For a deterministic process function it says: if w(000) = 000, then w(001) is 000 or 010, or w(100) = 000, or w(110) = 010, or w(111) = 011. It is a piece of combinatorial bookkeeping that every consistent deterministic loop obeys, and that mixtures therefore obey too. E_ex1 violates it: the left side is ½ and the right side is 0. Here is why. When everyone sends 0, the copier branch delivers 000, and that branch has probability ½. In each of the four situations on the right, neither the copier nor the negator delivers the listed inputs. For instance, when the outputs are 111 the copier delivers 111 and the negator 000, never 011.

Members of facet orbit 82 are violated by E_ex1 and by **all 51** sampled non-deterministic vertex orbits. So a single class of inequalities separates every sampled random corner from the hull. **Deriving it from purifiability is the natural next target. It has not been done.**

### 58. Walking from Lugano to E_ex1

The note also tests the boundary numerically (evidence; note D.8). Walk along the straight line from Lugano (purifiable) toward E_ex1 (not):

    x_t = (1 − t) · Lugano + t · E_ex1.

The process-function hull is left almost at once, at about t ≈ 2 × 10⁻⁷, because Lugano is a corner and this direction points straight out. The purification search finds nothing at t = 0.02 or t = 0.2, with best residuals 52.2 and 60.1. The same code reaches about 10⁻¹³ on Lugano itself. So along this line, purifiability appears to stop exactly where the hull does. That is consistent with the conjecture, but it is not proof.

### 58a. Two parties: there is nothing to purify away (proved; note Appendix G)

*A story first: the two-room house.* Two people live in a house with two rooms. Each can leave a note for the other, but the house has a rule: no note may ever create a paradox, whatever either of them decides to write. With only two rooms, it turns out the rule is very strict. In every run, one of the two must in effect read before the other writes, perhaps with a coin deciding who goes first. A genuine loop, where each reads what the other has not yet written, needs at least three rooms.

**The statement.** Write a two-party classical process as p(a, b | x, y). Here a is what Alice receives (her *input*), x is what she sends (her *output*), and b, y are the same for Bob. "Valid" means two things. Every probability is non-negative. And for every pair of strategies, Alice replying x = f(a) and Bob replying y = g(b) with *any* functions f and g, the probabilities of all consistent histories add up to exactly 1. The note proves (**Theorem G.1**) that every such p, with alphabets of any finite size, is a mixture of *causally ordered* process functions. In each of these, either Alice's input is fixed and Bob's is a function of what Alice sent, or the other way round.

**How the proof goes, in words.** Split p into pieces according to which of the four variables a, b, x, y each piece really depends on. Validity kills every piece that would let Alice's choice and Bob's choice interact inside the same input. What survives is a constant part, an "Alice-to-Bob" part and a "Bob-to-Alice" part. The constant part is large enough to cover the negative dips of the other two, so p splits into two non-negative halves: one where Alice goes first and one where Bob goes first. Each half is a mixture of deterministic one-way processes. This is the classical shadow of an argument by Oreshkov, Costa and Brukner (2012).

**Consequence.** For two parties, every valid classical process is a mixture of process functions. By Section 47 it is therefore purifiable. Both sides of the conjecture are true, so the conjecture holds, but trivially. The interesting question starts at three parties, which is where E_ex1 lives.

### 58b. Three parties with a clear order (proved; note Appendix H)

With three parties, Alice, Bob and Carol, there can be genuine loops (Lugano). But many three-party processes still have an order hidden in them. The note proves that whenever they do, the two-party result does the rest.

- **Someone is last (Theorem H.1).** Suppose Carol's output z changes nobody's input; she only listens. Then forget Carol for a moment. Alice and Bob form a valid two-party process, which by 58a is a mixture of ordered process functions. Carol's input is then just some random function of what Alice and Bob did. Every piece is a deterministic consistent loop, so the whole is a mixture of process functions.
- **Someone is first, properly (Theorem H.2).** Suppose Alice's input a does not depend on anyone's output (she is *marginally first*). Suppose also that, once a and Alice's output x are fixed, what remains between Bob and Carol is itself a valid two-party process (the *conditionals are valid*). Then each remainder is a mixture of ordered two-party process functions (58a). Gluing Alice in front gives a mixture of three-party process functions.

A process that is, in any run, a mixture of such "someone goes first, and the rest is consistent" pieces is called *causally separable*. So: **every causally separable three-party classical process is a mixture of process functions, and the conjecture holds for it** (trivially again: both sides are true).

**Where the real question is.** Lugano is not causally separable: it violates a causal inequality (Baumeler, Feix and Wolf, 2014), and each party's input depends on both others. So the open part of the conjecture lives exactly among the loops with no hidden order. That region contains Lugano-type process functions, their mixtures, and every candidate counterexample.

**A subtlety that matters.** "Marginally first" alone, without valid conditionals, is not enough. E_ex1, the coin-flip loop, gives each party an input that looks like a fair coin whatever anyone does. So every party is marginally first. Yet E_ex1 is not a mixture of process functions. Once you fix, say, Alice's input, the remaining Bob-Carol process can have no consistent history, or two.

### 58c. A tempting shortcut that fails (proved; note H.5)

Since E_ex1 and the hard orbits 7, 8 and 50 are all marginally first in some party, a tempting plan was: show that *purifiability* forces valid conditionals for a marginally-first party. Then 58b would finish them off.

*A story: the referee's coin.* A referee flips two coins, β and γ, and hands them to Bob and Carol as their inputs b = β and c = γ. Bob and Carol then each send a bit, y and z. Alice, last of all, is told a = β ⊕ γ ⊕ y ⊕ z, where ⊕ means addition mod 2 ("the parity"). In formula form,

    p(a, b, c | x, y, z) = ¼ if a = b ⊕ c ⊕ y ⊕ z, and 0 otherwise.

- This is a mixture of four deterministic consistent loops, one for each value of the coins (β, γ). In each, Bob and Carol go first and Alice last. So it is purifiable (Section 47).
- Looking only at the statistics, Alice's input is a fair coin whatever anyone does. She is *marginally first*, even though in the machine she is actually last.
- Fix Alice's input to a = 0 and look at what remains for Bob and Carol: (b, c) uniform among the pairs with b ⊕ c ⊕ y ⊕ z = 0. If Bob and Carol simply copy their inputs to their outputs (y = b, z = c), the "probabilities" of consistent histories add up to 2. For a = 1 they add up to 0. The conditional is not a valid process.

So the shortcut is false, already for a classically purifiable process. Every claim above is checked in exact fraction arithmetic (code/stochastic/structural/margfirst_cex.py). **Why the shortcut fails:** looking at a's statistics cannot tell you whether a is *computed first* in the machine. Fixing a is then post-selection, keeping only the runs where something downstream turned out a certain way, and post-selection does not respect reversibility. A version that might still be true would have to talk about the purifying unitary itself, not about W. That version is true; see 58d.

**Philosophical gloss (interpretation).** "Comes first" is a fact about mechanism, not about statistics. A variable can look exactly like a fresh coin flip while being the last thing the machine computes. This is the same lesson as Section 55, from the other side. There, the statistics looked like a coin tossed in advance, but no coin was in the drawer. Here, a party looks like it acts first and in fact acts last.

### 58d. The shortcut, repaired inside the machine (proved; note H.6)

58c showed that statistics cannot tell you who goes first. The machine can. Say Alice is *first in the machine* when her input wire is filled from the source alone, before anyone's output, her own included, can touch it. In the machine's own terms, the unitary splits into two stages. First a step that prepares Alice's input from the source. Then everything else.

*A story: the sealed envelope.* Before the game starts, the referee seals Alice's instruction in an envelope, using only the coins in her own pocket. Nothing Bob or Carol later does can reach back into that envelope. Opening it early is then just reading a note that was already written. It is not the post-selection of 58c, where we kept only the runs in which a later computation came out a certain way. So we may open the envelope first, write down a and Alice's reply x, and look at what is left between Bob and Carol. What is left is again a reversible machine of the same kind: a pure two-party process. Its statistics are exactly the conditional p(…)/p(a). So the conditionals are valid, 58b applies, and the whole process is a mixture of process functions.

Checks on the two running examples (code/stochastic/structural/opfirst.py):
- In the referee's-coin machine of 58c, Alice is *not* first in the machine; she is computed last, and her conditionals are invalid. Bob and Carol *are* first in the machine, and their conditionals are valid.
- In the Lugano machine nobody is first, and nobody can be. Lugano is not even marginally first in any party, so no machine for it puts anyone first.

**What this leaves.** A purifiable process outside the mixtures, if one exists, must have only machines in which *every* party's input is reached by somebody's output: a genuine loop, like Lugano's. Each of E_ex1 and the open orbits fails 58b's test in every party, so any machine for one of them would have to be loop-shaped all the way through. The conjecture now lives entirely there. The lemma is short, and close to known results on causal structure in unitary processes (Barrett, Lorenz and Oreshkov 2021). We did not find it stated in this form.

**Philosophical gloss (interpretation).** 58c said "first" is a fact about mechanism. 58d says that mechanism-level "first" is enough. Wherever the machine has a genuine first mover, chance inside the loop really is ignorance of which deterministic loop is running. The open question, whether chance can be basic inside a loop, is a question only about machines with no first mover at all.


### 58e. Machines with no first mover (evidence; note H.7)

58d leaves one place where a counterexample could hide: machines in which *nobody* is first. In such a machine, every party's input is touched by somebody's output. Here "the machine" means a purification: a reversible (unitary) device V that takes a source state and the parties' outputs, and returns the parties' inputs plus a sink record. We went looking for such machines with three parties sending and receiving single bits. For each one we asked whether the classical statistics it produces, p(i|o), can fall outside the mixtures of process functions (the "hull"). The answer from this search was **no, every time**. The search was small and local, so this is evidence, not proof.

Each machine found was given the same checks:
- *Is it pure?* Close each party's slot with random local unitaries and check that the result is still unitary.
- *Is anyone first?* For each party k, does any output reach k's input?
- *Who influences whom?* The full influence graph.
- *Is it in the hull?* A linear program measures the distance from p to the hull of the 744 process functions.
- *How much Lugano does it need?* The smallest weight that any decomposition of p must put on Lugano-type process functions. Weight 0 means p is an ordinary mixture of *ordered* process functions.

Four kinds of machine turned up. They have informal names here; the technical note gives the formal descriptions.

**The Ring** (single-function lifts). Lift one process function w as in Section 1. Party k's input is then w_k(o) plus a source bit, so k is first in the machine exactly when w_k ignores everyone's outputs. Of the 744 binary process functions, exactly 64 have no such constant part. They form a single family under relabelling: Lugano's orbit, in which each party's input is set by the other two parties' outputs. So, for lifts of a single function, "no first mover" means exactly "Lugano-type". Adding phases on the source alone or the sink alone keeps the machine pure. Phases that mix outputs and source destroy purity. Either way, the statistics are just w itself.

**The Chorus** (coherent blend of three causal orders; proved). Put three ordered process functions in coherent superposition, as in Section 47: one with Alice first, one with Bob first, one with Carol first. Inside this machine no party is first and no party is last. Yet the classical statistics are an ordinary mixture of ordered process functions.

*A story: the ledger with no clock.* Three clerks share an office with no clock. Ask any of them who signed the ledger first, and each will truthfully say that someone else's entry was already there. Yet each morning the ledger reads, page by page, as one of three tidy orders. The disorder lived inside the room. The record is ordinary.

The Chorus refutes a tempting guess: "every machine with no first mover is Lugano in disguise." That guess is false.

**The Switchboard** (a new family). The machine reads all three outputs o and picks one 8×8 unitary C_o for that joint choice. It applies C_o to a source register s, which produces the three input bits e. It also writes o, and e XOR'ed with a second source register t, into the sink:

    V|o, s, t> = sum_e C_o[e, s] |e> |o> |e xor t>.

Here |…> is a basis state, and the sum runs over the eight possible input strings e. The machine is always reversible, and the sink always keeps a copy of (outputs, inputs), so the statistics are classical: p(i|o) = |C_o[i, 0]|². Lugano is the special case where each C_o just flips bits according to w(o).

*A story: the switchboard.* Every caller's choice rewires the board before any call connects. Nothing is ever lost, because each board is unitary. The question is whether the boards for different choices agree well enough for the whole exchange to stay coherent. **Lemma H.7.1 (proved)** says exactly how much agreement is needed when the parties use no ancillas: a list of linear conditions on the products C_o C_o'†, one for each pair of different choices. With ancillas these conditions are still necessary, and Section 58f shows they are also enough. Whether the agreement forces an ordered story is open. It is a bet, not a proof.

**The Shadows** (three Switchboard machines found near Lugano). Starting the search close to Lugano produced three new pure machines (lug_21 to lug_23). Their C_o are generic unitaries, not relabelled permutations. Every party influences every other one. Their statistics need Lugano weight 0.87 to 0.93, so they are genuinely not causally separable, yet they lie inside the hull. One machine from a random start (rand_15) also has every party influencing every other, but its statistics need Lugano weight 0: like the Chorus, it is disordered inside and ordinary on the record.

**The numbers (evidence).**
- *What was run:* 11 random starts, 3 starts near Lugano, then polishing to high precision. That gave 13 pure machines in total. One random start never became pure. One was polished only to a residual of 1.6e-6.
- *Who is first or last:* 9 of the 10 pure random-start machines have a party that is first or last inside the machine, so 58d (first) or 58b (last) already covers them.
- *Hull:* every pure machine's statistics lie in the hull, at distance 0.
- *Pushing for a facet violation:* runs that also tried to push the statistics across a hull facet reached violations near the maximum, but only at purity residuals of 0.03 to 0.05. None was a pure machine.

**What this leaves open.** The conjecture for machines with neither a first nor a last mover. The Switchboard is one structured slice of them, and the Lemma is a foothold there. A general machine can have a bigger source and need not have this form.

**Philosophical gloss (interpretation).** The Chorus and the Shadows pull apart two things that are easy to run together: disorder *inside* the machine, and disorder *in the record*. A machine can be thoroughly cyclic inside while its record is an ordinary mixture of ordered stories. So far, every reversible loop we have found leaves a record that is a mixture of consistent deterministic loops.


### 58f. What the Switchboard's rules really say (proved in part; note H.8, C.6, Appendix I)

Section 58e left the Switchboard with a list of linear rules: the conditions under which its eight boards agree well enough to stay coherent. We now have a cleaner reading of those rules, and they turn out to be all the rules there are.

**The rules in plain words (proved).** Compare the boards for two different choices of outputs. The "difference" between them is the unitary K = C_o C_o'†. Like any operation on three bits, K can be written as a sum of simple pieces, each of which flips and/or phase-flips some of the three bits. (These pieces are the *Pauli strings*: X flips a bit, Z flips its sign, and a string says what happens to each of the three bits.) The rule is this: every piece of K must leave alone at least one of the parties whose output changed. For a process function, K is a single piece, and the rule becomes the exclusivity lemma of Section 1: two different output strings must agree at some party whose input they do not change. So the Switchboard's rule is exclusivity with a twist. A quantum board may be a *sum* of pieces that each leave a different party alone, where a process function must pick one. A computer check in exact fractions confirms that the old list and the new reading say the same thing.

**Ancillas do not matter (proved).** Section 58e said that private scratch qubits (ancillas) might impose extra conditions. They do not: in the Switchboard, purity with ancillas and purity without them are the same condition. So the 13 pure machines of 58e are exactly pure, not merely pure in the tests.

**Who is first, who is last (proved).** The rule also tells us, by inspection, who influences whom. A party is first exactly when no board difference ever touches its bit. A party is last exactly when changing its output only multiplies the board by a phase.

**The easy case is settled (proved).** If all the boards are just relabellings with phases (a common basis that each board only shuffles), then for *every* source state the statistics are a mixture of process functions. This covers the Ring of 58e. The hard case is boards that genuinely superpose, like a board that half-flips Alice's bit and half-flips Bob's at once. The Shadows are of this kind, and their statistics are still in the hull.

**How hard is it to cheat? (evidence).** We asked the computer to push a Switchboard's statistics across the most important wall of the hull (facet 82) by a set amount v, while staying as close to pure as it could. In 108 tries, the "impurity" R it had to accept was always at least about 0.31·v². In words: to get across the wall by v, you must be impure by roughly 0.56·v (measuring impurity as √R). Nothing found came closer. *(Superseded: Section 58h exhibits an exact machine that crosses a hull wall at zero impurity; the toll was an artefact of the search.)* If some machine could cross the wall at zero cost, the search would be closing in on a true counterexample, and it never did. This is evidence, not proof.

*A story: the toll on the wall.* The hull is a walled town. Every honest machine lives inside it. A traveller can always step up to the wall, and can even climb over, but each metre over the wall costs a fixed toll in impurity, and the toll never drops to zero. Whether the toll is a law of the land or only the price at the gates we have tried is the open question.

**Close to a mixture, close to liftable (proved, but easy).** If a process is close to a mixture of process functions, it is just as close to a liftable one, because the mixture itself lifts. The reverse, "close to liftable implies close to a mixture", is *exactly* the conjecture in disguise, so it cannot be proved separately. The meaningful version is the toll above: nearly pure machines give statistics nearly inside the hull.

**A dead end, checked before spending (evidence).** For orbit 8, a stronger kind of certificate (degree 4) was proposed: find a large slice of the space that contains no "forbidden" direction. Before renting any computer, we tested whether such a slice can exist at random. It cannot: random slices of the proposed size, and even smaller ones, all contain forbidden directions. So that certificate cannot be built that way, and nothing was spent.

**What is still open.** Whether the Switchboard's rule forces its statistics into the hull, and whether every machine with no first mover can be put in Switchboard form. Both are stated as conjectures in the technical note (H.9).


### 58g. Boards that blur two wirings (evidence; note H.10, H.11)

The hard Switchboards are the ones whose boards *blur* two flip patterns at once: partly "flip Alice's bit", partly "flip Bob's". We tried three ways to tame them.

**Shuffling does not help (proved).** One hope was to average the machine over harmless relabellings until the boards stop blurring. The only relabellings that leave all the statistics alone are phase changes on the input strings, and those leave the blur exactly as it was. So any proof has to face the blur directly.

**The cheapest kind of proof cannot work (proved).** A "degree-2" argument, which treats each board's entries only through averages of their products, cannot tell a real machine from a fake one that never relates different boards at all. That fake can produce any statistics whatever. So a proof has to be at least degree 4 in the board entries.

**A whole family, checked exactly, then tested (evidence).** The simplest blurring boards mix two process functions with a fixed angle: "mostly w1, a little of w2", coherently. The computer listed *every* way to choose w1 and w2 so that the Switchboard's rule holds. (Along the way it confirmed that, for single bits, the exclusivity rule singles out exactly the 744 process functions.) There are 39,512 such pairs, and 34,304 of them genuinely blur. For every one of their 237 symmetry types, at seven angles, and against *all* 29,344 walls of the hull, the statistics stayed inside the hull for every source state. The worst value was −0.00000000000002, which is zero up to rounding. This is evidence, not proof. No counterexample.

**Is every no-first-mover machine a Switchboard? (partly proved).** Any machine can be given an extra "carbon copy" of the inputs in its sink without spoiling its purity. A slightly bigger Switchboard, with extra sink space, obeys the same rule, piece by piece. What is missing is one fact: that the machine's sink can always be made to remember the parties' outputs, whatever the source holds, and not just for the source state actually used. If that fact holds, every no-first-mover machine is a Switchboard, and the conjecture comes down to the Switchboard rule. We could neither prove that fact nor break it.

*A story: the two-tone bell.* A bell-founder casts bells that ring two notes at once. Each note on its own is a tune the town knows. The worry is that the two notes, ringing together, could beat into a tune no one has heard. Every bell of the simplest two-note kind has now been rung against every wall of the town, and none has carried a new tune out. Whether some three- or four-note bell could do it is still unknown.


### 58h. The bet is lost: a reversible loop with genuine chance (proved; note H.12, H.10.6)

**First, a win (proved).** The two-tone bells of 58g are now settled: *every* two-pattern Switchboard gives statistics that are a mixture of process functions, for every angle and every source state. The proof is a bookkeeping trick. For each board, the machine only ever moves probability around inside small blocks of input strings, and it moves the total in each block nowhere. So one can "ship" the source's probabilities to the board's probabilities block by block. Each way of shipping, combined over the different boards, turns out to be a process function. A computer checked, exactly, that this works for all 39,512 two-pattern boards.

**Then a loss (proved).** Allowing all eight flip patterns at once changes the picture. The computer found a Switchboard whose eight boards are built only from the phases 1, i, −1, −i in the Hadamard basis. Every one of its rules checks out exactly, in exact arithmetic with no rounding. For one simple source state, its statistics are a *valid* classical process: every intervention gives total probability exactly 1. Yet that process lies **outside** the hull of process functions. There is a wall of the hull that every process function respects, and this process sits on the wrong side of it, by exactly 3√2/16 − 1/4 (about 0.015). So the conjecture this note has been chasing is **false**: a reversible quantum machine can produce classical statistics in a time loop that are *not* a disguised mixture of consistent deterministic loops.

**Why the earlier search missed it.** The big search over all boards kept settling into local valleys (Section 58f's "toll" was one of them). Restricting to boards built from flips alone made the landscape simple enough that exact solutions appeared at once. The toll was the price at the gates we happened to try, not a law of the land.

**How sure are we?** Three separate checks now agree.
1. *The note's own proof.* The facts about the classical statistics (valid, outside the hull) are exact. Purity follows from the switchboard lemma and its two companions (H.7.1, H.8.1, H.8.2), proved on paper, together with an exact check of the rule.
2. *An independent referee.* Someone else wrote a fresh verification program working only from the note's description of the machine. It checks purity directly, without using those lemmas. It recounts the 744 process functions from scratch and finds its own wall that the process crosses. It agrees on every point (note H.12.2).
3. *A proof assistant.* The whole statement, "there is a valid, purifiable classical process outside the hull of process functions", has been proved in Lean (note H.12.3).

**What "checked by a proof assistant" means here.** Lean is a program that accepts a proof only if every step follows from the rules of logic and from earlier proved facts. It does not trust the author or take a step on faith, and it is the incorruptible referee of Part VI. Its verdict is only as good as the definitions it was given. Here the definitions of "pure", "valid" and "process function" were written for this one proof, in a small self-contained file. A careful reader should still check that they mean what this guide says. Two limits are known.
- The scratch equipment in each lab is assumed finite.
- These definitions have not yet been formally connected to the general framework that the main theorem's Lean proof uses.

Inside those limits the counterexample is as certain as mathematics gets. It has not been through peer review.

**What changes.** The "if" half stands: every mixture of process functions is purifiable. Two parties, and three parties with an order or with a first mover, still give nothing new. The new statement is: *quantum reversibility is strictly more permissive than classical reversibility for classical loops, already with three parties and one bit each.* Classically (D.6), reversibility does force the hull.

*A story: the three-note bell.* The founder finally cast a bell with eight notes. Each pair of notes was in tune with the town's rules, and every rule held to the last digit. When it rang, it played a tune that no deterministic loop could play, yet a tune no one could catch in a contradiction. Chance, it seems, can live inside a consistent loop, provided the loop is quantum.

**Philosophical gloss (interpretation).** Section 64 asked whether chance inside a loop can be fundamental, or only ignorance about which deterministic loop obtains. For classical reversible machines the answer is still "only ignorance". For quantum reversible machines it is now "not always".


---

## Part XI. The honest map of dead ends

### 59. A story: the cartographer's other map

Explorers publish the route that reached the summit. The best of them also publish a second map, of the gullies that ended in cliffs, the passes that were snowed in, and the bridges that looked sound and were not. That second map is less glamorous, but it is the one the next party needs most.

The "only if" half of the conjecture, open until Section 58h, had such a map. Here it is, route by route. Every entry is either **proved** to be a dead end, or **evidence** that it stalls.

### 60. The routes that failed

1. **The hidden-label route. Dead end, proved (D.4).** Find a classical "which loop" variable in the source. The causal counterexample of Section 55 shows that no such variable need exist, even when the conclusion is true.
2. **The weaker quantum test. Dead end, proved (D.5).** Demand only that probabilities be normalised under quantum-controlled interventions. Every classical process passes, including E_ex1 (Section 56).
3. **The actual source state. Dead end, proved (D.2, D.8).** Look only at what the purification does to the source state that is really prepared. Every classical process passes there too, so no certificate built from that data alone can rule out a purification (Section 56).
4. **Single-form certificates. Partial success, then a stall.** Combine the constraint forms into one and count its plus and minus directions (Section 50). This *works* for the two smallest orbits, giving E_ex1's exact certificate. For the 49 larger orbits it was inconclusive.
5. **Block forms and semidefinite relaxations. Stalled.** Matrix-valued forms and semidefinite programming generalise the counting test. The note's Section 9 lists them, with single-form inertia, as the attempts that "stalled for the larger orbits".
6. **Symmetry and representation theory. Negative result (Appendix E).** The 384 symmetries (permuting parties, relabelling inputs and outputs) could shrink the problem, so the note computed each process's *stabiliser*, the symmetries that leave it unchanged. E_ex1 and orbit 50 have 48, orbit 7 has 16, Lugano 6, and 34 of the sampled orbits have only the trivial one. Symmetry helps most exactly where certificates already exist, and not at all for most open orbits. Worse, the natural convex relaxation that symmetry would have sped up, a moment relaxation over pairs of copies of the projector, turned out to be *feasible* for E_ex1 at r = 16, with strict margins. It cannot even detect the one case we know is non-purifiable. It is strictly weaker than the plain counting test, so symmetry-reducing it is pointless. Stronger convex certificates would need higher moment levels, or would have to encode rank.
7. **Local numerical search. Evidence, not proof.** Gradient searches find Lugano's purification and stall on every random corner tried (Sections 51 and 58). A local search can always miss a solution.
8. **Algebraic geometry. Assessed: infeasible by size** (code/stochastic/alggeom/SIZE_ESTIMATES.md). Why not just solve the equations directly? Purifiability asks for a 16-dimensional subspace on which every constraint form vanishes, which is a system of polynomial equations. The forms are sesquilinear, so the system lives over the real numbers. Written out in coordinates, E_ex1 has 352 real unknowns and 23,552 real quadratic equations. Orbit 8 has about 2,112 unknowns and 100,352 equations. Homotopy continuation, the standard numerical method, would have to track about 2³⁵² solution paths for E_ex1 and 2²¹¹² for orbit 8. And certifying that *no* solution exists is exactly the hard case for such methods. Gröbner bases, the exact method, are far out of reach: practical limits are tens of variables, not thousands. Symmetry does not reduce the number of unknowns, because the subspace sought need not itself be symmetric. Small sub-problems are feasible but uninformative: isotropic subspaces exist for small r, and non-existence only starts near r = 15–16, where the full size applies. So the obstruction will not yield to brute-force elimination. It needs a structural argument, or a stronger convex hierarchy (route 6).

9. **Rank (determinant) bound for orbit 8. Fails, numerically (note H, route B).** If u is in a subspace that makes every form vanish, the whole subspace sits inside the vectors "orthogonal" to u under all forms. Counting those gives a dimension bound. But vectors of the isotropic set exist for which the bound allows about 28–32 dimensions, more than the 16 needed. So one vector is not enough.
10. **Form certificates for orbits 8, 10, 20. Proved too weak (note C.5).** Every linear or block combination of the forms tried stalls. Adding the normalisation provably adds nothing. Numerically, subspaces making all forms vanish exist up to dimension about 10, short of 16, but the gap is non-convex and invisible to such certificates. The earlier estimate that about half of the open orbits could be certified this way is withdrawn.
11. **Marginally first implies valid conditionals. Dead end, proved (H.5; Section 58c).** (The machine-level version is true: Section 58d.)
12. **Counterexample hunt from the quantum side. No hit (note H, route C).** Searching directly over unitaries for a purifiable process outside the hull found none. Starting from Lugano, every step outside the hull cost purity.

### 61. Why the dead ends cluster

The map has a shape, and the shape is the lesson.

- **The easy information is useless.** Everything readable from the actual source state is satisfied by every classical process (routes 2 and 3). Any proof must use how the purification would treat source states orthogonal to the one actually prepared.
- **That information is non-convex.** Demanding that a whole 16-dimensional (or larger) subspace make many quadratic forms vanish at once is not a convex condition. Convex questions can usually be settled by duality: when no solution exists, there is a checkable certificate saying so. Non-convex questions offer no such guarantee. Every convex surrogate tried, routes 4 to 6, either needs luck in small cases or is provably too weak. Attacking the non-convex system head-on (route 8) is hopeless by sheer size.
- **No shortcut through a hidden variable** (route 1). The argument has to work at the level of the statistics W, presumably facet by facet (Section 57).

When this map was drawn the conjecture was open. D.3 is refuted, and the conjecture itself was later refuted by Section 58h, through a route this map did not list: restricting the search to flip-built Switchboards.

**Philosophical gloss (interpretation).** Negative results are knowledge. "This route provably cannot work" narrows the space of possible proofs as surely as a positive lemma narrows the space of possible worlds. Here the negative results also have content of their own. They say that what separates basic chance from ignorance, if anything does, lies in the *counterfactual* behaviour of a reversible world, how it would have treated a source state that was never prepared. Nothing in what actually happens shows it.

---

## Part XII. Philosophical discussion

> **Everything in this part is interpretation.** It is a reading of the results above, following the note's own philosophical sections (3–8 and the end of 9). None of it is a theorem. Where a claim goes beyond the note's own wording, I say so.

### 62. Consistency plus a complete record gives unitarity

The classical demand "exactly one consistent history, whatever anyone does" was invented to dissolve the grandfather and the bootstrap. Nothing in it mentions amplitudes, phases or interference. Yet the main theorem shows that, together with one more ingredient, it is enough to keep the quantum lift unitary. The extra ingredient is the sink's *complete record*: its perfect copy of every party's output (Sections 18 and 28). Because the sink records the outputs, each final state corresponds to a single history, and histories cannot interfere on the way to the same record. Consistency then guarantees that any two global histories are told apart by some agent who was in the same situation in both. Quantum mechanics turns "told apart by a local agent" into "orthogonal", and that orthogonality, between records that already separate the histories, is what unitarity needs.

The note's own slogan is that fixed-point consistency is "already a quantization condition". The more careful statement is: **consistency plus a complete record gives unitarity.** Consistency alone does not, since the bare loop w (Lugano, say) is not even reversible; the source and sink must be added first. The note surveys other quantum treatments of time loops. Deutsch's fixed-point model pays for its consistency with nonlinearity. Post-selection discards inconsistent branches, which the note calls a filter on samples, "of the same shape as a measure-zero axiom". Neither, the note argues, supplies the criterion. For process functions, the theorem shows that no extra quantum filter is needed. Once the world keeps a complete record, the classical consistency condition, imposed for all interventions, carries over.

### 63. Lewis and Novikov, revisited

Lewis showed that time travel stories need not contradict themselves. Novikov proposed that physics admits only the stories that do not. Both left a gap. Lewis's "can and cannot" explains why the grandfather survives, but not *which* history obtains. Novikov's principle throws out inconsistent histories but does not choose among the consistent ones. The billiard balls of Section 3 often had infinitely many.

The process-function clause closes both gaps at once, at the price of a strong demand. *Every* intervention must have exactly one consistent history. The main theorem then adds something neither Lewis nor Novikov could have asked for. When the agents are given every power quantum mechanics allows, the demand still holds, with probabilities exactly normalised, for finite and countably infinite alphabets alike. On this reading, the consistency principle is not a filter bolted onto the dynamics, which was Earman's worry. For process functions, it *guarantees a property of a reversible dynamics* that contains the loop. (The converse, that every inconsistent loop breaks unitarity, is supported numerically but not proved; Section 36.)

### 64. Can chance be fundamental inside a loop?

Two pictures of chance are in play.

- **Chance as ignorance.** The world is in a definite, deterministic state. Probabilities express what we do not know. In a loop, this means there is a definite consistent deterministic loop, and we are unsure which.
- **Chance as basic.** The world itself is chancy. No more definite story underlies the probabilities.

The polytope separates these pictures geometrically. Mixtures of process functions are ignorance. The random corners, such as E_ex1, are consistent loops whose chance cannot be read as ignorance over consistent deterministic loops.

The results so far:

- In a *classical* reversible world, only ignorance-chance is possible (D.6, proved).
- In a *quantum* reversible world, ignorance-chance is possible (C.1, proved), and at least some basic-chance loops are impossible (E_ex1, and every vertex in orbits 7 and 50, one of which contains E_ex1; proved).
- *Not* every basic-chance loop is impossible in a quantum reversible world: the conjecture is false (Section 58h, proved). Some are possible, and some (E_ex1) are not.

**What this teaches (interpretation).** Purity does not single out the mixtures of deterministic loops. Quantum reversibility is strictly more permissive than classical reversibility, which does single them out (D.6). The extra loops need three labs, since with two every consistent chancy loop is already a mixture (Section 58a). In them no lab goes first inside the machine: by Section 58d, a machine with a first mover only produces mixtures. Chance can be basic in a loop, but only in a loop that is cyclic all the way down.

*The reading below was written assuming the conjecture and is superseded.* If the conjecture held, the note's reading would be this. Every reversible quantum loop with classical statistics is a coherent ignorance-mixture of deterministic consistent loops. Genuinely chancy loops like E_ex1 would be classically consistent but not reversibly realisable. **Reversibility, not consistency alone, would be the constraint that excludes basic chance from loops.** D.5 sharpens this: consistency under all quantum interventions holds for every classical process, so it is precisely the reversibility requirement that does the excluding.

### 65. Determinism hidden, or created on the fly?

There are two ways to imagine the chance in a mixture of loops.

- **Hidden determinism.** The world was always one particular deterministic loop. The coin was tossed at the beginning and its face is written somewhere. We just have not looked.
- **Determinism created on the fly.** No face is written anywhere. A definite loop *emerges* as the agents act, and which one emerges depends on what they do.

The clockmaker's workshop (Section 53) is pure hidden determinism: the shuffled deck in the drawer. The D.4 counterexample (Section 55) shows that a quantum reversible world can produce the very same statistics by the second route. The token answers "which loop?" only when asked, and the question it is asked depends on Alice's choice.

**Interpretation (written assuming the conjecture; superseded by Section 58h for loops outside the hull).** If the conjecture were true, the two pictures cannot be told apart by any loop's classical statistics. Every quantum-reversible chancy loop has the statistics of a shuffled deck. But the *mechanism* may still be on-the-fly. The ignorance reading is safe as a claim about W. It is not safe as a claim about a hidden label. This is the note's own caveat. That it echoes contextuality in quantum foundations (Kochen and Specker) is my comparison, not a result.

### 66. Reversibility and the arrow of time

Section 21 gave the standard picture: reversible laws, an arrow supplied by a special beginning and an accumulating record. The lift realises that picture precisely, for loops.

- In the middle is U, reversible, with M unitary however the agents act.
- At the beginning is the source, set to a fixed state.
- At the end is the sink, which keeps a perfect record of what the parties sent and received (D.1, Section 56), and which we then ignore.

Randomness appears only at the edges. A mixture of loops arises from a coherent source and a discarded record (Section 47). If the label is not handed to the sink, the branches interfere, and the result is no longer a classical mixture. **Interpretation.** In this toy world, classical chance and the arrow of time have a common origin: what we do not track at the boundaries. The conjecture, read this way, says that boundary-ignorance is the *only* source of chance a reversible loop can have. That is why basic chance, as in E_ex1, would be excluded not by consistency (E_ex1 is consistent) but by reversibility. Section 58h refutes that reading. Interference among the board operations inside the machine, not only ignorance at the boundaries, can produce classical chance in a reversible loop. Reversibility still excludes some basic chance, such as E_ex1, but not all of it.

### 67. Freedom, bilking and Lewis

Black's *bilking* argument against backward causation goes like this. If a later event causes an earlier one, an agent who sees the earlier event can act to prevent the later one. Either the agent cannot so act, which wants explaining, or the later event was not needed for the earlier one. Lewis answered that the agent can and cannot, in two senses of "can".

The process-function framework takes a definite side. It quantifies over *all* interventions, so no action is forbidden. The loop only constrains which global history results. The note is explicit that this does not settle whether the agent's choice was genuinely *open*. The fixed-point clause says the choice, if made, completes uniquely. Whether that answers Black depends on whether a consistency condition may rule out interventions, or only rule out histories given the interventions. The note takes the second reading, and the formalism is built for it: consistency never forbids an intervention. As the note's Section 5 puts it, "Consistency is not allowed to forbid the operation. It is allowed only to constrain the global solution."

### 68. Time symmetry and the reading of the source and sink

Read forwards, the source is an input and the sink is an output. Read backwards, using U†, they swap roles, and the reversed operator is the time-reversed process. In a loop like Lugano, an earlier input already depends on a later setting. Some authors, notably Price, argue that time symmetry pushes toward retrocausality. Leifer and Pusey made that argument precise under an assumption ("λ-mediation"), and Maudlin has objected to it. The note's position is modest. The mathematics does not choose between a retrocausal reading and a merely operational time-reverse. It does remove one cheap reply: one cannot say that the cyclic classical model dies as soon as the agents act quantumly.

### 69. What formal verification adds, epistemically

**Interpretation.** A proof does two jobs. It *convinces* (this is true), and it *explains* (this is why). Machine-checking strengthens the first job enormously and leaves the second untouched. The Lean files guarantee that the stated theorem follows from the stated definitions. They do not tell you why exclusivity is the heart of the matter. That is what Parts II–V are for.

Machine-checking also changes the *social* character of trust. Without it, a reader trusts the author, the referees, and the hope that someone would have noticed a gap. With it, a reader can trust a small public kernel and two lines of definition, and needs no one's reputation. That suits a result about consistency well. Its claim is that a loop is safe when every agent's every choice completes uniquely, and its warrant is a check that every inference completes.

Two cautions. First, a checked theorem is only as good as its statement (Section 39). Second, the parts that matter most philosophically, the readings in this Part, are exactly the parts no referee, human or mechanical, can check.

### 70. What the theorem does not say

- **It is not about spacetime.** See "How to read this" at the top: a unitary dilation is not a spacetime.
- **It does not classify all quantum processes.** It places every process function, including ones that violate causal inequalities, among the unitarily extendible processes. It says nothing about processes that are not deterministic classical functions, beyond the stochastic results of Parts VIII–XI.
- **It does not cover continuous alphabets.** Countable ones are done (Part VII). Continuous ones are settled for point-moving local operations and for causal loops (F.5); the general non-causal case still needs a definition.
- **It does not settle freedom** (Section 67).
- **The weak point is the lemma.** The combinatorial lemma is the piece an attacker has to break. Everything after it is row orthogonality. In this case the lemma is also machine-checked, and it holds for alphabets of any size.

### 71. How big is the purifiable set? (H.13)

The H.12 counterexample can be made much plainer. A board that uses only signs (±1) gives a counterexample in which every number is a simple fraction such as 1/16 or 9/16. The source state is just (|000>+|001>+|010>-|101>)/2. Each step between boards mixes 4 classical patterns instead of 8. This was checked in exact fraction arithmetic. Mixing two purifiable processes always gives a purifiable process: a hidden coin decides which purification runs. So the purifiable set is convex. It sits strictly between the mixtures of process functions and the valid processes. A complete search of one natural family of boards (13,105 boards) shows which facets of the hull can be crossed and roughly by how much. 31 of the 93 facet types were never crossed. These are numerical leads, not theorems.

### 72. Where the line falls (H.14)

A board whose steps each mix at most three classical flip patterns of the plain (X-only) kind can never leave the hull. This is now proved, so four patterns is exactly where X-only counterexamples start. Allowing eighth roots of unity instead of fourth roots crosses 8 more facet types of the hull. Those crossings are checked in exact arithmetic. 23 facet types have still never been crossed. The largest crossings found have exact values such as (√17−3)/8. The pattern suggests, without proving it, that the purifiable set has a curved boundary and is not a polytope.

### 73. Putting it in spacetime: three time travellers and a quantum loop (H.15)

**The stage.** General relativity allows spacetimes with closed timelike curves, for example wormholes whose mouths are out of step in time. Baumeler, Costa, Ralph, Wolf and Zych showed that three agents, each in an ordinary small lab, can sit around such a loop. Each can be both in the past and in the future of the others, and each stays free to do whatever they like. No grandfather paradox ever arises. The loop's job is to return to each lab, in its past, a bit computed from what all three sent out. The allowed rules are exactly the "process functions" of this note. Every such rule can be built from reversible machinery, for example billiard balls bouncing inside the wormhole region.

**Story 1: the classical loop.** Ana, Ben and Cai each find a bit on their doorstep, think, and post a bit into the wormhole. A hidden billiard-ball computer decides what lands on the doorsteps, so that whatever they do, history stays consistent. If the computer's starting position is random, they see a random mixture of consistent histories. These mixtures are the "hull".

**Story 2: the quantum loop.** Now let the machinery inside the loop be quantum and perfectly reversible: nothing is ever erased, and everything that goes in comes out somewhere. This is what "purifiable" means. Our counterexamples show that the statistics Ana, Ben and Cai record can then fall outside every mixture of consistent classical histories. They can test it: run many rounds, histogram the bits, and add them up with the integer weights of one facet. Classical loops always give zero or more. The simplest quantum loop we found gives minus one-eighth, using only plus and minus signs. That number is a fingerprint of quantum time travel, not just of time travel.

**Story 3: what the loop must look like.**
- Nobody can be first. If any one lab could be placed at the start of the loop, the fingerprint would vanish (H.6).
- The loop obeys a strict traffic rule. When some of the travellers change what they send, the loop's response must leave at least one of them untouched (the Pauli rule, H.8).
- Simple loops are not enough. A loop that mixes at most three plain bit-flip patterns at each step can always be faked by a random classical history. Four are needed (H.14).

**Story 4: no wormholes.** In ordinary flat spacetime, with no time travel, a similar experiment would need the three "labs" to be smeared out in time, and it would have a hidden step-by-step explanation (Vilasini and Renner). There, the fingerprint would not show time travel. It would show that the hidden explanation must itself be coherently quantum.

**What is solid and what is not.** The mathematics is proved. The papers cited were checked on arXiv. The reading as time travel is an interpretation within one model of quantum time travel; other models (Deutsch's) differ. No actual spacetime or device realising our loop has been constructed.

### 74. Smooth dials instead of switches, and the full facet tables (F.5, Appendix J)

**The question.** So far every party's setting was a whole number, like a switch with finitely or countably many positions. What if it is a dial, a real number or an angle?

**Story.** Ana, Ben and Cai each turn a dial. A loop returns to each of them a dial setting that depends on the others. Before, we counted possibilities: "on average, exactly one consistent history" was the heart of the proof. With dials there are uncountably many histories, so counting has to become measuring volume.

**What we proved.**
- Take any consistent loop and suppose each person only shifts, flips or stretches their dial (and may add a phase). Then the closed loop squeezes no volume and loses none. So it is a perfectly reversible quantum operation, even when nobody is first.
- The trick is to peel off one person at a time. Once everyone else's part of the history is fixed, the loop has to hand the remaining person a fixed setting; otherwise two different histories would both be consistent. Peeling the people off in turn turns "one history on average" into "volume preserved".
- If the loop is causally ordered, any quantum operation at all works.
- What is left open: for loops with no order, and for operations that mix positions completely (like a Fourier transform), there is not yet a natural definition of what closing the loop even means.

**Machine checks.** The peeling lemma is checked in Lean for dials of any kind. The counterexample of Part VIII now uses the same definitions as the rest of the Lean proofs.

**The tables.** Appendix J of the technical note lists every one of the 93 kinds of facet, the walls of the classical region. For each kind it gives an explicit integer inequality, how many walls are of that kind, and how far our quantum loops get past it. The 23 kinds that no loop we tried ever crossed are listed separately; that is a numerical finding, not a proof.

---

## What is proved, what is evidence, what is open

> **Proved**
>
> - **A purifiable process outside the hull** (H.12; Section 58h). Exact counterexample to the purification conjecture. It is the note's main result. Purity follows from the paper lemmas H.7.1, H.8.1 and H.8.2. The whole statement was re-derived independently (H.12.2). *Machine-checked in Lean as `purification_conjecture_false`, standard axioms only.* The limits are finite ancillas and self-contained definitions not yet linked to the main framework (H.12.3).
> - **Two-tone Switchboards are mixtures** (H.10.6; Section 58h). Coset-transport theorem plus an exhaustive exact check of all 39,512 two-pattern boards.
> - **The main theorem.** Every process function, with any finite alphabets, lifts to a pure unitary process: under any local unitaries with any finite ancillas, the source-to-sink map is unitary. *Machine-checked in Lean 4 (exclusivity lemma; M M† = 1 and M† M = 1; unitary-group membership), standard axioms only.*
> - **Validity under everything.** Validity under arbitrary local operations, entangled or shared ancillas, and instruments follows by Stinespring, and so does the process-matrix normalisation Tr[W(…)] = 1. *Machine-checked in Lean, finite dimensions: `PFUL.valid`, `PFUL.valid_kraus`, `PFUL.valid_instrument`, `PFUL.Choi.bornC_anc_eq_one` and the group-free `PFUL.Choi.bornAnc_eq_one`, the equivalence `PFUL.Choi.afnb_iff_density` (and `_split`), Choi's theorem `PFUL.Choi.isCP_iff_choi`, all bundled in `PFUL.Choi.validity_package`.*
> - **Countable alphabets** (Appendix F). With finitely many parties and countable alphabets, the inputs carrying a group structure, the lift is unitary on ℓ². Rows come from exclusivity, and unit columns from the expected-number-of-fixed-points argument, which also gives a dimension-free finite proof. *Machine-checked in Lean, ending in `PFUL.Countable.induced_unitary_l2`. The finite-alphabet column proof is checked too.*
> - **Mixtures.** Mixtures of process functions are purifiable: a coherent random source, with the label recorded in the sink.
> - **The classical version.** Classical reversible purifiability holds exactly for mixtures of process functions (D.6). By the counterexample, quantum reversibility does add something.
> - **Certificates.** E_ex1 and the vertex orbits 7 and 50 (one of which contains E_ex1) are not purifiable. *Exact rational certificates, not Lean proofs.*
> - **Structure.** In any purification, the sink holds an orthogonal record of (outputs, inputs) (D.1).
> - **The dead ends.** Constraints on the fixed source state alone are vacuous (D.2). Validity under quantum-controlled interventions holds for every classical process (D.5). The hidden-label strengthening D.3 is false, with a causal circuit as counterexample (D.4). No certificate that uses only the fixed source state can rule out purification of any classical process (D.8).
> - **Two parties** (Appendix G; Section 58a). Every two-party valid classical process is a mixture of ordered process functions, so for two parties purifiable means mixture; the counterexample needs three.
> - **Ordered three-party processes** (Appendix H; Section 58b). If some party is last, or first with valid conditionals (causally separable), the process is a mixture of process functions.
> - **A shortcut closed** (H.5; Section 58c). Purifiable plus marginally first does not force valid conditionals; exact counterexample.
> - **The Chorus** (H.7; Section 58e). A machine with no first or last mover can still produce an ordinary mixture of ordered process functions, so "no first mover" does not mean "Lugano in disguise". The Switchboard's no-ancilla purity condition (Lemma H.7.1) is proved, and it is the full purity condition: it reads as operator-valued exclusivity, and ancillas add nothing (H.8; Section 58f). Relabelling-type Switchboards give mixtures of process functions.
> - **The shortcut repaired at machine level** (H.6; Section 58d). If some purification has a party first *in the machine* (its input prepared from the source alone), the conditionals are valid and the process is a mixture of process functions.
> - **Facets.** The three-party binary process-function hull has exactly 29,344 facets in 93 orbits (exact computation with normaliz).
>
> **Negative results (Appendix E)**
>
> - Symmetry stabilisers are large only where certificates already exist. Most open orbits have trivial or tiny stabilisers.
> - The moment relaxation is feasible for E_ex1 at r = 16, so it is strictly weaker than single-form inertia, and symmetry-reducing it is pointless.
> - Algebraic geometry on the full system is infeasible by size: 352 real unknowns and 23,552 equations for E_ex1, and about 2,112 and 100,352 for orbit 8, with about 2²¹¹² homotopy paths (code/stochastic/alggeom/SIZE_ESTIMATES.md).
>
> **Evidence (not proof)**
>
> - A GPU search found no purification for any of the 49 remaining sampled non-deterministic vertex orbits. Best residuals were 12.97–59.35.
> - Machines with no first mover (H.7; Section 58e): a small, local search found 13 pure machines, including the Shadows near Lugano. All of their statistics lie inside the hull.
> - Two-tone Switchboards (H.10; Section 58g): all 39,512 two-pattern boards allowed by the rule, checked against every hull wall at seven angles, stay inside the hull for every source state. Float64 evidence, no counterexample. Proved: no relabelling trick and no degree-2 argument can settle the general case.
> - ~~Switchboard toll (I.4; Section 58f)~~: withdrawn. It was an artefact of local search; H.12 crosses the hull at zero impurity.
> - Degree-4 certificates for orbit 8 of the proposed shape cannot exist for random slices (C.6). No paid compute was used.
> - A single facet orbit (82) is violated by E_ex1 and by all 51 sampled non-deterministic vertex orbits.
> - Along the segment from Lugano to E_ex1, purifiability appears to stop exactly where the hull does.
> - Orbits 8, 10, 20: isotropic subspaces appear to stop near dimension 10, short of the 16 needed; form certificates provably cannot capture this (C.5). A unitary-side counterexample search found nothing (H.3).
> - Numerically, non-process functions fail unitarity under random local unitaries (2- and 3-party binary). The converse of the main theorem is not proved.
>
> **Open**
>
> - **The conjecture: refuted (H.12; Section 58h).** "Purifiable iff a mixture of process functions" is false. The "if" half is proved; the "only if" half fails for an exact three-party binary Switchboard. It is proved on paper, re-checked independently and proved in Lean, with the limits stated above. Open now: what the purifiable set actually is (a polytope?), the smallest counterexamples, other scenarios, and linking the Lean definitions to the main framework.
> - **Loops without a first mover.** Which processes are purifiable among those whose purifications all have no party first in the machine (H.6; Lugano-type loops; the Ring, Chorus, Switchboard and Shadows of Section 58e), and the exact status of orbits 8, 10, 20 and the other 46 sampled open orbits.
> - **Facets from purifiability.** No facet inequality, for example orbit 82, has been derived from purifiability.
> - **Where any non-purifiability proof must look.** Any proof must use the purifying unitary on source states orthogonal to the actual one. That is the non-convex isotropy condition of Araújo et al.'s Theorem 4, where every certificate attempt has stalled for the larger orbits: single-form inertia, block forms, SDP and moment relaxations.
> - **Continuous alphabets.** Settled for point-moving local operations and for causal loops (F.5, paper proof; core lemma in Lean). Open for non-causal loops with general local operations.
> - **Not formalised.** The literal Choi form Tr[W(…)] = 1 in infinite dimensions, where W is not trace class. The trace form is checked: the project's own trace-class and partial-trace library (`lean/PFUL/TraceClass.lean`) gives `PFUL.Countable.valid_density_l2`, Tr = 1 for every input density operator on ℓ².
> - **Not addressed.** Spacetime embedding, and lifts built from bijections other than U.

*For definitions, full proofs, references and code pointers, see the technical note, [paper/lift.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/paper/lift.md), and [lean/STATUS.md](https://github.com/drewarrowood/process-function-unitary-lift/blob/main/lean/STATUS.md).*

## 75. Plain-language note: what the computer now checks about smooth dials (Oct 23 2026)

Section 74 described inputs that are smooth dials (a position on a line or an angle on a circle) rather than finite menus. Two of its key facts are now checked line by line by the Lean proof assistant, using only the standard axioms.

- **No volume is lost or gained.** Wire the parties into any loop, causal or not. The map from "what everyone outputs" to "the net shift around the loop" moves regions of outcome space around without changing their total size. This is the continuous replacement for "exactly one consistent history" in the finite case. The computer proves it for any number of parties on lines, circles, or any group with a translation-invariant notion of size.
- **Probabilities still add to one.** If every party just shifts its dial and adds a phase, the whole loop is a unitary. Total probability is conserved for every input state.
- **The counterexample is tied to the standard formalism.** The Switchboard's purity, the key ingredient of the counterexample to the purification conjecture, is now shown to be a property of its process matrix W = |V⟩⟩⟨⟨V|. That is the object the rest of the theory uses.

Not yet checked by computer: local operations that stretch the dial (these need a Jacobian change of variables), memories (ancillas) that are infinite-dimensional, and the automatic boundedness of physical maps.

## 76. Plain-language note: helpers of unlimited size (Oct 23 2026)

Before this round, the computer checked the Switchboard counterexample only when each outside "helper" system had finitely many settings. Helpers may now have countably infinitely many settings, such as an infinite ladder of levels. The computer checks that the combined process still loses no information: it is an isometry, meaning it preserves lengths and angles. It also checks that the new definition gives the same answer as the old one whenever the helpers are finite, and the counterexample to the purification conjecture holds in this stronger form. Two things are still open. The computer has not shown the stronger statement that the process is fully reversible (unitary) for infinite helpers. The links to the general validity definition and to general smooth reparametrisations are also still open.

## 77. Plain-language note: the helper machine is fully reversible, and smooth dials work too (Oct 23 2026)

Last round, the computer checked that our helper construction never loses information when the helper is unlimited. Now it also checks that the construction can be run backwards, so it is fully reversible. This means the counterexample survives the strictest reading of "purifiable".

The computer also checks the "smooth dial" result for any smooth, one-to-one rearrangement of space. Stretching and squeezing are fine, provided the rearrangement never crushes a region flat.

Two puzzles are still open:
- the boards that are not of the X type;
- the 23 inequalities that no test has broken yet. (Note 78 shows one of them is just "probabilities are never negative", so 22 are genuine.)

## 78. Plain-language note: attacking the two open puzzles (Oct 23 2026)

This round attacked the two open puzzles: switchboards that are not of the X type, and the 23 inequalities no test had broken, of which 22 turn out to be genuine (paper Appendix H.17).

- **Non-X switchboards exist.** These are reversible switchboards with up to three terms per setting that are not of the X type. The computer built more than 20,000 of them, and every one stayed inside the region spanned by ordinary process functions. This is a computer check, not a proof.
- **A small theorem.** One way such a board could escape is through a "sign flip" between two settings of the same dial. An exhaustive exact check proves this can never fit into a full three-party board, as long as the dial settings are generic.
- **Validity alone is not enough.** For 22 of the 23 inequalities we have exact counterexamples that satisfy every consistency rule but break the inequality. So any proof of those 22 must use reversibility (purifiability), not just consistency. The last one (number 92) turned out to be simply "probabilities are never negative". An exact certificate now proves this, so it holds for every process. It should never have been on the open list.
- **Wider searches.** Finer phase dials, continuous dials and local rotations of each party broke none of the 22 genuine inequalities.

- **Half a proof for non-X boards.** The old argument for X-type boards carries over to every board whose "reachable flips" form a closed group. This part is proved. For three-term dials the reachable flips are {none, A, B}, and the flip "A then B" is not covered automatically. That last finite check is what remains.

- **The last check, done.** A complete computer enumeration of every way two dials can sit side by side found 329,280 local trouble spots. All but 288 of them provably cannot fit into a full three-party board. An exact search over every possible full board then showed that the last 288 cannot fit either. So every such board with generic dial settings is proved to be a blend of fixed-point machines. Boards with finely tuned dial settings, where terms cancel, are different. Of the 37 tuned boards the search found, 35 fail the test, so the proof does not reach them, although all 37 still sit inside the blend region numerically. A second trick handles them. First fold one dial's setting into the starting state, then run the same test on what is left. That variant is proved to work whenever it passes. We rebuilt 18 tuned boards, plus one saved earlier, and all 19 pass it, so each of them is proved to be a blend. A computer also found the blend recipe explicitly for each. We then listed every way the terms of two dials can cancel. Dials built on different term sets cannot cancel at all. Dials sharing all their terms cancel in only a few ways, and that list is proved. Dials sharing half their terms can lose one term, a result checked numerically. A further 32 tuned boards also pass, 51 in all. Most of them turned out not to be really tuned at all: the search had given the same dial two names. Every genuinely tuned board found shrinks to the simple one-switch type once one dial is folded into the starting state. Still unproved: that this holds for every tuned board. That needs rerunning the exhaustive search with the cancellation list, the next step.

Still open: a proof covering every finely tuned board (all 19 checked pass), and the 22 genuine inequalities in general.
