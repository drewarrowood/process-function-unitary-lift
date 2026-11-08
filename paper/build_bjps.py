#!/usr/bin/env python3
"""Build paper/bjps.pdf and paper/bjps-title.pdf."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="bjps-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"bjps.tex", work/"bjps.tex")
        latex(work, "bjps", 3)
        shutil.copy(work/"bjps.pdf", PAPER/"bjps.pdf")
        if (PAPER/"bjps-title.tex").exists():
            shutil.copy(PAPER/"bjps-title.tex", work/"bjps-title.tex")
            latex(work, "bjps-title", 1)
            shutil.copy(work/"bjps-title.pdf", PAPER/"bjps-title.pdf")
    print("wrote", PAPER/"bjps.pdf")

if __name__ == "__main__":
    main()
