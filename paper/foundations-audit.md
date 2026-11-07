# Claim-to-source audit for the Foundations draft

This note is for review. It is not part of the manuscript. The manuscript is `paper/foundations.tex`. Nothing in `paper/lift.md`, `paper/graded.md`, `docs/lift.pdf`, `docs/graded.pdf`, `essay.md`, or `paper/essay/` was edited. `main` and `bookkeeping` were not updated. The draft branch is the only destination.

## Counts (typeset PDF)

- Pages: 12, letter, about 1 inch margins (text from x ≈ 72 pt to x ≈ 542 pt on a 612 pt page).
- Abstract: 210 words (journal guidance 150–250).
- Keywords: 5.
- Words from the introduction through the end of the discussion, before the declarations: about 4,900. Words in the whole PDF, including appendices and references: about 6,600.
- Editorial budget in the brief was 7,000–9,000 words of main text and about 20–25 pages. That budget is not a journal limit. The draft is shorter because the infinite-party development, the Lean index, and the search logs were left in the archive on purpose. Padding to the budget would have repeated that archive.

## What is claimed, and where it comes from

| Claim in the draft | Status in the archive | Where |
|---|---|---|
| Every finite process function lifts; the closed loop is unitary for every local unitary and finite ancilla | Proved; machine-checked | `paper/lift.md` §1; `PFUL.induced_unitary` |
| The converse: unitarity for every such test iff the map is a process function | Proved; the old “converse without ancillas is only sampled” remark in §1 is superseded later in the same file | Theorem 1.2; `PFUL.CopyGadget.unitary_iff_pf` |
| Exclusivity lemma | Proved in §1; equivalent to the process-function definition for finitely many parties | Lemma in §1; induction in the archive (L-121 and following) |
| Purity implies validity under instruments | Proved by Stinespring in Appendix A of the archive; machine-checked package | `PFUL.Choi.validity_package` |
| Mixtures of process functions are purifiable; Purif is convex | Proved (coherent label / block-diagonal sum) | C.1; H.13.1 |
| A three-party binary classical process from the switchboard is valid, pure, and outside conv(PF), with value 1/4 − (3/16)√2 | Proved by exact arithmetic and by Lean | H.12.1; tables copied from H.12 and `gTab` in `CounterexampleData.lean` |
| The underlying board is a frame-rotated time reverse of a √X-Lugano purification, not a newly discovered quantum board | Settled in the archive (H.21.2). An earlier “maybe a new board” question is closed | §0 novelty note |
| “Purifiable iff a mixture of process functions” | Refuted. Earlier sections that call it open are marked superseded in the archive | H.12.1 |
| Two parties: valid classical processes are mixtures of ordered process functions | Proved in archive Appendix G; known in substance | Oreshkov–Costa–Brukner 2012; Baumann–Brukner 2016 |
| Some valid processes are not purifiable (E_ex1, orbits 7 and 50) | Exact certificates in the archive (C.2). Not re-derived in this draft. The draft says so | H.13.1 |
| LP distance ≈ 0.0607 | Numerical, not used as a proof | H.12 |
| Infinite-party exclusive map with no fixed point | Proved in ZFC; mentioned only as a boundary | L-233 |
| Baire-class-1 exclusive ⇒ fixed point | Open. Not claimed | archive §10 and later notes |

## Left out on purpose

Lean labels L-001–L-321 as a list; countable-closed and G-delta theorems; perfect-set padding; prefix normalizers; facet-orbit searches; stochastic optimisation logs; the gentle version’s stories; essay material. The draft points to the archive commit `154eec44e2b26b12d4e0f091185a0e9f70750c4c` instead.

## Declarations not filled in

Affiliation, email, ORCID, funding, competing interests, and acknowledgments are marked pending. They are not invented. Generative assistance is disclosed as Grok Bot, a Cursor cloud agent, beyond copy editing, with author verification still pending.
