# Audit for the Journal of Philosophy-style draft

Private working note. Not part of the review manuscript. No submission is requested or recorded. This draft is not claimed to be ready for submission.

## Status

Branch `cursor/jphil-draft-cc9c`, taken from `main` at `47f9f8ee2c9b65becd619eb70891ce46ed1d872a`. This commit does not update `main`, the public site, or `bookkeeping`.

The argument is not the Synthese draft retitled. That draft separates consistency, causal order, reversibility, purification, and time-travel explanation. This draft’s claim is about computational implementation and modal warrant: universal consistency is a compositional admissibility condition. It is not an efficient dynamics, a physical implementation, or a bridge to metaphysical possibility.

## Counts

Counted from the built review PDF with `pdftotext` (all text, including abstract, keywords, notes, appendix, and references): **9501 words**. Journal maximum, rechecked this turn on the Memo to Authors, is 12,000 words all-in. Editorial target 9,500–10,500 is not a journal rule.

Abstract: **120 words** (source count). Keywords: three (`computational implementation`, `consistency`, `causal order`). PDF: **14** letter pages, about one-inch margins, text about 72–542 pt on a 612 pt page. Review PDF author metadata is empty. No archive URL in the review PDF.

## Rules rechecked

https://www.journalofphilosophy.org/memotoauthors.html was opened this turn. Confirmed: 12,000-word all-in maximum; abstract at most 150 words; at least two keywords; page numbers; reference list; triple-anonymous review with a separate title page carrying names, affiliation, email, ORCID, acknowledgements, funding, AI use, and conflicts; Word or PDF; no prescribed LaTeX class or citation style; no primarily historical or expository articles; no contact with editors other than the managing editor. None of that contact was made. Formatting for accepted articles is said to be supplied later and was not imitated.

Recent Journal volumes were not surveyed. The brief’s older sample (Schaffer 2000 and 2001) was not re-opened in this authoring pass. No 2026 house style is inferred from it.

## What was read

- Chalmers, “Does a rock implement every finite-state automaton?”, *Synthese* 108 (1996), 309–333, from the author’s HTML text. Used for strong conditionals, the clock-and-dial point about inputless automata, combinatorial state automata with components in distinct regions, and his admission that some astronomical false implementations remain. He is not described as requiring one globally first component.
- Piccinini, “Computing mechanisms,” *Philosophy of Science* 74 (2007), 501–526, from the UMSL faculty PDF. Used for the function of producing output strings by a general rule, mechanistic explanation by parts and organization, digits, malfunction, and the digestion comparison.
- Anderson and Piccinini, *The Physical Signature of Computation* (Oxford, 2024): the published abstract of the robust-mapping chapter (DOI `10.1093/9780191872075.003.0006`) and the book record. The chapter body was not available. The information-theoretic criteria discussed in a book review were not attributed to them.
- Leibniz, *Monadology*, Bennett’s modernized rendering (earlymoderntexts.com), sections 17, 31–38, 53–59, and 78–81. No quotation. “Greatest variety” with “order” is section 58 of that rendering. Bennett’s editorial additions are not treated as Leibniz’s words.
- Turing, “On computable numbers,” *Proceedings of the London Mathematical Society* s2-42 (1937), 230–265, from the Virginia-hosted scan of the journal pages. Checked the opening (definable numbers need not be computable; a machine writes the decimal), §1 (finite m-configurations, one scanned square, limited human memory), the circular/circle-free definition (finite versus infinite output figures of the first kind, not physical loops), and the universal machine supplied with a description on the tape. No quotation in the manuscript. The 1938 correction was identified on Crossref and not re-read.
- Aaronson and Watrous, *Proceedings of the Royal Society A* 465 (2008), 631–647: Crossref abstract only. Polynomial-space power is taken from that abstract and is not transferred to process functions.
- Baumeler et al., *Classical and Quantum Gravity* 36 (2019), 224002: abstract previously checked and the DOI reconfirmed. Used for reversible realization inside their classical process theory, including three parties each in the others’ past and future.
- Baumeler and Wolf, *New Journal of Physics* 18 (2016), 013036: bibliographic record. The Lugano rule and the process-function definition are the standard ones in that literature and in the unpublished note.
- Vilasini and Renner, *Physical Review A* 110 (2024), 022227: title and DOI. Cited only as no-go results about embedding cyclic information-theoretic structures in acyclic spacetimes. Their proofs were not re-derived.
- SEP “Computation in Physical Systems” was used to locate Chalmers and Anderson–Piccinini. It is not cited as a substitute for those texts.

Not read, and not given detailed positions: Sider, Baron and Colyvan, Lewis’s 1976 article, the body of Araújo, Guérin, and Baumeler on indefinite-causal computation. No constant-overhead simulation theorem is stated.

## Technical limits

The canonical equivalence is for the source-sink permutation tested against every local unitary and every matched finite ancilla. The bare permutation exists for rules that are not process functions. The computational-basis witness uses a known board; `L(p)=1/4-(3/16)√2<0`; it is not a new board and not a basis-independent exclusion. Baire class one is open and appears only as a footnote. Finite explicit tables are treated as brute-force searchable. No new complexity, hypercomputation, consciousness, or grounding claim is made. The model defeats a stated entailment. It does not prove a physically or metaphysically possible machine. This session did not re-run Lean.

## Anonymity and assistance

The review PDF has an empty author field and no archive address. It says related drafts are already public, so anonymity is not claimed. The title page carries the name, the pending declarations, and the disclosure that Grok Bot, a Cursor cloud agent, did generative drafting beyond copy editing. Underlying model and provider beyond that description are not invented. Author verification is pending.

## Preservation

`paper/lift.md` SHA-256 `7ca6d4b619081c70c9b46111e2e9213f3b05b0f184c21ec69cfafdaa1ce634b6` on `main` and on `bookkeeping`. `paper/graded.md`, Foundations and Synthese sources and PDFs, and the site files match `origin/main`. `bookkeeping` was not moved.
