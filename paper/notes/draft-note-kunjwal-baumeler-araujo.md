# DRAFT, NOT SENT. Do not send without Drew's review.

**From:** Drew Lamarr Arrowood
**To:**
- Ravi Kunjwal, Aix-Marseille Université (LIS, CANA team), Marseille. Email: *not found in a public source*; contact via https://ravikunjwal.com/ [affiliation from his homepage, Oct 2026; UNVERIFIED as current]
- Ämin Baumeler, Università della Svizzera italiana (Faculty of Informatics), Lugano. amin.baumeler@usi.ch [from the USI staff directory and PRX Quantum 4, 040307; UNVERIFIED as current. An older Vienna address, aemin.baumeler@univie.ac.at, appears on an old Quantiki post and is probably stale]
- Mateus Araújo, Universidad de Valladolid (Ramón y Cajal researcher, Dept. of Theoretical, Atomic and Nuclear Physics and Optics). mateus.araujo@uva.es [from the UVa Portal de la Ciencia; UNVERIFIED as current]

**Subject:** Purifiable classical processes vs. mixtures of process functions: status and a question

Dear Ravi, Ämin and Mateus,

I've been working on a question that grows out of your work on purification of processes (Araújo, Feix, Navascués, Brukner 2017) and on classical processes and process functions (Baumeler–Wolf). The conjecture: a classical process (a point of the Baumeler–Wolf polytope) is purifiable if and only if it is a mixture of process functions. Here is where it stands. The write-up is at https://drewarrowood.github.io/process-function-unitary-lift/ (Section 9 has the status map).

- **Settled.** Every process function lifts to a unitary process (machine-checked in Lean, including countable alphabets), and so every mixture of process functions is purifiable. Two parties: the conjecture holds, since every bipartite valid classical process is a blend of causally ordered process functions (essentially known from OCB 2012 and Baumann–Brukner 2016). Three parties, the conjecture also holds when some party is last, and when the process is causally separable.
- **Operator-first result (H.6).** If some purification has a party whose input is prepared from the source alone, then every conditional bipartite process is valid and purifiable, and the process is a mixture of process functions. So a counterexample would need a purification in which every party's input is influenced by some party's output. Lugano-type cyclic lifts have this property.
- **Certificates (C.5, D.9).** E_ex1 and vertex orbits 7 and 50 have exact rational inertia certificates of non-purifiability. For orbits 8, 10 and 20, the linear and block-Hermitian form certificates stall, and the obstruction looks non-convex. Facet orbit 82 of the PF hull is violated by every non-hull vertex we sampled. I have not been able to derive it from purifiability. Such a proof must use the purifying unitary on source states orthogonal to the fixed one, i.e. the isotropy condition of AFNB Theorem 4.
- **Cyclic families (H.7, numerical).** With three binary parties, a search over purifications with no operator-first party found pure purifications with complete causal graphs beyond Lugano. These include one with a separable W and a non-separable continuous family near Lugano. Every induced classical process lies in the convex hull of the process functions.

My question: do you know of a counterexample (a purifiable classical process that is not a mixture of process functions), or of results that settle or constrain the cyclic case? Pointers to anything I have missed in the literature would also be very welcome.

Thank you for your time, and for the work this builds on.

Best regards,
Drew Lamarr Arrowood
