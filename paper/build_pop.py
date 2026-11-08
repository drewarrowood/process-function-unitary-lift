#!/usr/bin/env python3
"""Build paper/pop.pdf and paper/pop-title.pdf. Does not touch other manuscripts."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work: Path, stem: str, n: int) -> None:
    for _ in range(n):
        subprocess.run(["lualatex","-interaction=nonstopmode","-halt-on-error",f"{stem}.tex"], cwd=work, check=True)

def main() -> None:
    with tempfile.TemporaryDirectory(prefix="pop-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"pop.tex", work/"pop.tex")
        latex(work, "pop", 3)
        shutil.copy(work/"pop.pdf", PAPER/"pop.pdf")
        shutil.copy(PAPER/"pop-title.tex", work/"pop-title.tex")
        latex(work, "pop-title", 1)
        shutil.copy(work/"pop-title.pdf", PAPER/"pop-title.pdf")
    print("wrote", PAPER/"pop.pdf")

if __name__ == "__main__":
    main()
