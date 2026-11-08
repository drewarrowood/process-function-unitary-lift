#!/usr/bin/env python3
"""Build the Journal of Philosophy-style review draft.

Writes paper/jphil.pdf from paper/jphil.tex and paper/jphil.bib,
and paper/jphil-title.pdf from paper/jphil-title.tex.

Does not read or write the technical note, the gentle version,
the Foundations draft, the Synthese draft, or the site.

    python3 paper/build_jphil.py
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


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="jphil-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER / "jphil.tex", work / "jphil.tex")
        shutil.copy(PAPER / "jphil.bib", work / "jphil.bib")
        _latex(work, "jphil", 1)
        subprocess.run(["bibtex", "jphil"], cwd=work, check=True)
        _latex(work, "jphil", 3)
        shutil.copy(work / "jphil.pdf", PAPER / "jphil.pdf")
        shutil.copy(PAPER / "jphil-title.tex", work / "jphil-title.tex")
        _latex(work, "jphil-title", 1)
        shutil.copy(work / "jphil-title.pdf", PAPER / "jphil-title.pdf")
    print("wrote", PAPER / "jphil.pdf")
    print("wrote", PAPER / "jphil-title.pdf")


if __name__ == "__main__":
    main()
