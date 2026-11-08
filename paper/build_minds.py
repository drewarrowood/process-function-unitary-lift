#!/usr/bin/env python3
"""Build paper/minds-machines.pdf and the title page."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="minds-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"minds-machines.tex", work/"minds-machines.tex")
        latex(work, "minds-machines", 3)
        shutil.copy(work/"minds-machines.pdf", PAPER/"minds-machines.pdf")
        shutil.copy(PAPER/"minds-title.tex", work/"minds-title.tex")
        latex(work, "minds-title", 1)
        shutil.copy(work/"minds-title.pdf", PAPER/"minds-title.pdf")
    print("wrote", PAPER/"minds-machines.pdf")

if __name__ == "__main__":
    main()
