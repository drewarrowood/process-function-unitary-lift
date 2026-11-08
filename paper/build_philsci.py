#!/usr/bin/env python3
"""Build paper/philsci.pdf and paper/philsci-title.pdf."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work, stem, n):
    for _ in range(n):
        subprocess.run(["lualatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main():
    with tempfile.TemporaryDirectory(prefix="philsci-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"philsci.tex", work/"philsci.tex")
        latex(work, "philsci", 3)
        shutil.copy(work/"philsci.pdf", PAPER/"philsci.pdf")
        if (PAPER/"philsci-title.tex").exists():
            shutil.copy(PAPER/"philsci-title.tex", work/"philsci-title.tex")
            latex(work, "philsci-title", 1)
            shutil.copy(work/"philsci-title.pdf", PAPER/"philsci-title.pdf")
    print("wrote", PAPER/"philsci.pdf")

if __name__ == "__main__":
    main()
