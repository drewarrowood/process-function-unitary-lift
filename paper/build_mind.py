#!/usr/bin/env python3
"""Build the Mind-style review draft.

Writes paper/mind.pdf from paper/mind.tex, and paper/mind-title.pdf
from paper/mind-title.tex.

Does not read or write the technical note, the gentle version, the
Foundations draft, the Synthese draft, the Journal of Philosophy draft,
or the site.

    python3 paper/build_mind.py
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
    with tempfile.TemporaryDirectory(prefix="mind-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER / "mind.tex", work / "mind.tex")
        _latex(work, "mind", 3)
        shutil.copy(work / "mind.pdf", PAPER / "mind.pdf")
        title = PAPER / "mind-title.tex"
        if title.exists():
            shutil.copy(title, work / "mind-title.tex")
            _latex(work, "mind-title", 1)
            shutil.copy(work / "mind-title.pdf", PAPER / "mind-title.pdf")
    print("wrote", PAPER / "mind.pdf")


if __name__ == "__main__":
    main()
