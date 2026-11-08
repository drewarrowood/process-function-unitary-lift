#!/usr/bin/env python3
"""Build paper/philstudies.pdf and the title page."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="ps-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"philstudies.tex", work/"philstudies.tex")
        latex(work, "philstudies", 3)
        shutil.copy(work/"philstudies.pdf", PAPER/"philstudies.pdf")
        shutil.copy(PAPER/"philstudies-title.tex", work/"philstudies-title.tex")
        latex(work, "philstudies-title", 1)
        shutil.copy(work/"philstudies-title.pdf", PAPER/"philstudies-title.pdf")
    print("wrote", PAPER/"philstudies.pdf")

if __name__ == "__main__":
    main()
