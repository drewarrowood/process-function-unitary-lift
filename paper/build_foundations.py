#!/usr/bin/env python3
"""Build paper/foundations.pdf from paper/foundations.tex.

Uses lualatex (STIX Two Text / STIX Two Math when the engine is LuaLaTeX).
Does not touch docs/lift.pdf or docs/graded.pdf.

    python3 paper/build_foundations.py
"""
from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "paper" / "foundations.tex"
OUT = ROOT / "paper" / "foundations.pdf"


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="foundations-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(SRC, work / "foundations.tex")
        for _ in range(2):
            subprocess.run(
                ["lualatex", "-interaction=nonstopmode", "-halt-on-error", "foundations.tex"],
                cwd=work,
                check=True,
            )
        shutil.copy(work / "foundations.pdf", OUT)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
