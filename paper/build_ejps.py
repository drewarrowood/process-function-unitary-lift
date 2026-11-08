#!/usr/bin/env python3
"""Build paper/ejps.pdf and paper/ejps-title.pdf."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="ejps-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"ejps.tex", work/"ejps.tex")
        latex(work, "ejps", 3)
        shutil.copy(work/"ejps.pdf", PAPER/"ejps.pdf")
        shutil.copy(PAPER/"ejps-title.tex", work/"ejps-title.tex")
        latex(work, "ejps-title", 1)
        shutil.copy(work/"ejps-title.pdf", PAPER/"ejps-title.pdf")
    print("wrote", PAPER/"ejps.pdf")

if __name__ == "__main__":
    main()
