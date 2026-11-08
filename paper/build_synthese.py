#!/usr/bin/env python3
"""Build the Synthese-style review draft.

Writes paper/synthese.pdf from paper/synthese.tex and paper/synthese.bib,
and paper/synthese-title.pdf from paper/synthese-title.tex.

Does not read or write paper/lift.md, paper/graded.md, paper/foundations.*,
docs/lift.pdf, docs/graded.pdf, or docs/foundations.pdf.

    python3 paper/build_synthese.py
"""
from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"


def _latex(work: Path, stem: str, passes: int) -> None:
    for _ in range(passes):
        subprocess.run(
            ["lualatex", "-interaction=nonstopmode", "-halt-on-error", f"{stem}.tex"],
            cwd=work,
            check=True,
        )


def build_review(work: Path) -> None:
    shutil.copy(PAPER / "synthese.tex", work / "synthese.tex")
    shutil.copy(PAPER / "synthese.bib", work / "synthese.bib")
    _latex(work, "synthese", 1)
    subprocess.run(["bibtex", "synthese"], cwd=work, check=True)
    _latex(work, "synthese", 3)
    shutil.copy(work / "synthese.pdf", PAPER / "synthese.pdf")


def build_title(work: Path) -> None:
    shutil.copy(PAPER / "synthese-title.tex", work / "synthese-title.tex")
    _latex(work, "synthese-title", 1)
    shutil.copy(work / "synthese-title.pdf", PAPER / "synthese-title.pdf")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="synthese-pdf-") as tmp:
        work = Path(tmp)
        build_review(work)
        build_title(work)
    print("wrote", PAPER / "synthese.pdf")
    print("wrote", PAPER / "synthese-title.pdf")


if __name__ == "__main__":
    main()
