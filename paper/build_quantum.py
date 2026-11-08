#!/usr/bin/env python3
"""Build paper/quantum.pdf with the bundled quantumarticle class.

Does not upload to the arXiv and does not touch other manuscripts.
"""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def run(cmd, work):
    subprocess.run(cmd, cwd=work, check=True)

def main() -> None:
    with tempfile.TemporaryDirectory(prefix="quantum-pdf-") as tmp:
        work = Path(tmp)
        for name in ("quantum.tex", "quantum.bib"):
            shutil.copy(PAPER/name, work/name)
        engine = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "quantum.tex"]
        run(engine, work)
        run(["bibtex", "quantum"], work)
        run(engine, work)
        run(engine, work)
        shutil.copy(work/"quantum.pdf", PAPER/"quantum.pdf")
    print("wrote", PAPER/"quantum.pdf")

if __name__ == "__main__":
    main()
