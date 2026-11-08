#!/usr/bin/env python3
"""Build paper/shps.pdf and paper/shps-title.pdf."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["lualatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="shps-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"shps.tex", work/"shps.tex")
        latex(work, "shps", 3)
        shutil.copy(work/"shps.pdf", PAPER/"shps.pdf")
        if (PAPER/"shps-title.tex").exists():
            shutil.copy(PAPER/"shps-title.tex", work/"shps-title.tex")
            latex(work, "shps-title", 1)
            shutil.copy(work/"shps-title.pdf", PAPER/"shps-title.pdf")
    print("wrote", PAPER/"shps.pdf")

if __name__ == "__main__":
    main()
