# Process functions and a unitary lift

Draft. Not a preprint. Not refereed.

**Claim.** For every classical process function w, the source/sink permutation unitary U|o,e⟩ = |w(o)+e, o⟩ is a valid unitary quantum process. Composed with arbitrary local unitaries, it induces a unitary from source to sink.

- Paper (canonical source): [paper/lift.md](paper/lift.md). PDF built from it: [paper/lift.pdf](paper/lift.pdf) (`python3 paper/build_pdf.py`).
- Lean: [lean/](lean/), main theorem `PFUL.induced_mul_conjTranspose` in [lean/PFUL/UnitaryLift.lean](lean/PFUL/UnitaryLift.lean), status in [lean/STATUS.md](lean/STATUS.md). That file states exactly what is machine-checked and what is assumed.
- Numerics: [code/check.py](code/check.py). It enumerates all binary 2- and 3-party process functions, checks unitarity under Haar-random local unitaries (with ancillas, plus ternary examples), and checks that non-process functions fail.
- Embedding status (not a spacetime metric): [paper/EMBEDDING.md](paper/EMBEDDING.md).
- The long essay lives in [drewarrowood/process-function-essay](https://github.com/drewarrowood/process-function-essay). `paper/essay.md` and `paper/essay/` are an older copy, kept unchanged.

Older HTML/PDF drafts were removed on branch `cleanup-and-proofs`; they remain in git history.
