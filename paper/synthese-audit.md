# Audit for the Synthese-style draft

Private working note. Not part of the review manuscript. No submission is requested or recorded.

## Status

Branch `cursor/synthese-draft-cc9c`, drafted from `main` at `14f5b888c3fb0a1d465f55a6cd7fd0aaa4118192`. This commit does not update `main`, the public site, or `bookkeeping`. The three published versions stay byte-for-byte as on that commit.

The review manuscript is a philosophical argument. The same three mathematical results also appear in `paper/foundations.tex` and in the technical note. Those are alternative treatments of one body of research, aimed at different readers. This note does not claim either treatment is the unique statement of the results, and it does not ask Drew to choose a submission. None has been requested.

## Official rules rechecked

Fetched this turn from https://link.springer.com/journal/11229/submission-guidelines (journal 11229):

- Double-anonymized review. Separate title page for name, affiliation, correspondence, acknowledgements, disclosures, and funding. Self-citation in the third person when one's own work must be mentioned.
- Abstract 150–250 words, no undefined abbreviations or unspecified references.
- 4–6 keywords.
- Statements and declarations; competing interests are required for a real submission. Unknown items are left pending rather than invented. Submissions that lack relevant declarations are returned as incomplete, so the pending status is stated instead of a fabricated "no conflict."
- LLM use beyond copy editing is documented in the manuscript (a methods section or a suitable alternative), not only on the title page. Copy editing alone would be exempt. This draft's assistance was generative, so it is declared.
- Decimal headings, at most three levels. Footnotes, not endnotes. A footnote may mention a cited work but is not citation-only.
- Author–year citations, alphabetical reference list, italic journal titles, full DOI links where a DOI was verified. The list includes only works that are published or accepted and that are cited. Unpublished work is mentioned in the text only.
- No prescribed word or page limit. Typical length 15–30 printed journal pages. The editorial target of about 9,000–11,000 words and about 18–24 pages is not a rule.
- No survey articles, response papers, or brief discussion notes. The draft leads with its own argument.
- Editable LaTeX source plus PDF. The Springer Nature template is recommended, not stated as the only acceptable class. This draft uses a standard article class that compiles.

## Counts on the built PDF

- Abstract: 239 words.
- Main text, approximate count from the source before the appendix: about 9,700 words.
- Appendix: about 900 words.
- `paper/synthese.pdf`: 18 letter pages, 11 pt, about one-inch margins. Text on sampled pages sits near x = 71–543 pt on a 612 pt page. The last reference page reaches about x = 543 pt. No missing-glyph markers in the extracted text.
- Keywords: six.

## What was actually read

- Adlam (2023), author manuscript (Chapman Digital Commons and the PhilSci copy of the same paper), including the process-function exposition, the partial-explanation passage on consistency, and Appendix A on time reversal. The published DOI and the Synthese volume/article number were confirmed on Crossref. Page numbers of the published typesetting were not used.
- Loewenstein (2022), PhilArchive penultimate draft ("Forthcoming at Synthese"). The published abstract matches. Arguments about Lewis, Ismael, and the remaining inexplicability are taken from that draft. Published page numbers were not used. The draft's bibliography lists Smith (2017), while a quotation in the body is tagged 1997. Smith is not cited.
- Lewis (1976), the American Philosophical Quarterly text, from a PDF whose first page identifies *American Philosophical Quarterly*, April 1976, Vol. 13, No. 2, pp. 145–152. The compossibility analysis, the other sniper, and the fatalist rejoinder are from that text. Crossref did not return a DOI for the 1976 printing. The 1987 reprint DOI is recorded only as a reprint note.
- Baumeler, Costa, Ralph, Wolf, and Zych (2019), Crossref abstract only: reversible realization of deterministic dynamics compatible with arbitrary local operations, including three parties each in the others' past and future. The body of the paper was not read. The claim that they left a quantization conjecture open is not used.
- Araújo, Feix, Navascués, and Brukner (2017), Crossref abstract only: the purification postulate and the definition of a pure process as inducing a unitary from past to future when local unitaries are applied. Crossref DOI `10.22331/q-2017-04-26-10`. The Foundations draft cited `10.22331/q-2017-04-25-10`, which Crossref does not resolve. This draft uses the Crossref DOI.
- Oreshkov, Costa, and Brukner (2012); Baumeler and Wolf (2016); Guérin and Brukner (2018); Vilasini and Renner (2024): titles, venues, and DOIs confirmed on Crossref. No theorems are quoted from their bodies beyond what those titles and the Adlam text support. The frame identification of the witness board is attributed to the unpublished technical note, which names the Guérin and Brukner family.
- Sider (2002) and Baron and Colyvan (2016): Crossref bibliographic records and DOIs only. The review manuscript attributes claims to them only as Loewenstein reports those claims, and it says so.
- Ismael (2003): Crossref record and DOI. The article was not read. The manuscript does not quote it. It reports Loewenstein's use of it.
- The mathematical statements are taken from `paper/foundations.tex` on `main` (`14f5b88`), which was read. They are not re-proved from Lean in this draft.

## Omitted rather than treated as published

Daher Ahmed and Kunjwal, arXiv:2610.00579 (2026), and Dourdent, Leitherer, Boghiu, Simonov, Kunjwal, and Acín, arXiv:2609.39735 (2026), appear in the Foundations draft. They were not independently checked for this manuscript. They are not cited and are not relied on. The lifting theorem is stated as a result of the unpublished note. Baumeler et al. (2019) are cited only for the classical reversible realization in their abstract.

## Anonymization

The review PDF has an empty author field and no archive or website address. The surname Arrowood appears in the third person, which is the journal's own instruction for citing one's own unpublished work. A masked reviewer link for the proofs and the code has not been prepared. The manuscript says so. It does not invent an anonymous repository.

## Overlap

`paper/foundations.tex` states the finite-alphabet lift, the restricted all-local-unitary converse, and the computational-basis witness outside the process-function hull, for a physics readership. This draft uses those three results as evidence for a different claim: consistency under the stated interventions can coexist with failure of a fixed causal order; the reversible extension is not a time-travel license; purification in a named basis does not restore the deterministic hull. The old mixture conjecture is described as refuted in the three-party computational-basis case and as open for the rest of the purifiable set. Baire class one is left open. The board is not claimed to be new.

## Preservation

Checked against `origin/main` and, for `paper/lift.md`, against `origin/bookkeeping`:

- `paper/lift.md` SHA-256 `7ca6d4b619081c70c9b46111e2e9213f3b05b0f184c21ec69cfafdaa1ce634b6` on both.
- `paper/graded.md`, `paper/foundations.tex`, `paper/foundations.md`, `paper/foundations.pdf`, `docs/lift.pdf`, `docs/graded.pdf`, and `docs/foundations.pdf` match `origin/main`.
