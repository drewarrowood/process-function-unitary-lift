#!/usr/bin/env python3
"""Build paper/erkenn.pdf and paper/erkenn-title.pdf. Does not touch other manuscripts."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def latex(work: Path, stem: str, n: int) -> None:
    for _ in range(n):
        subprocess.run(["lualatex", "-interaction=nonstopmode", "-halt-on-error", f"{stem}.tex"], cwd=work, check=True)

def main() -> None:
    with tempfile.TemporaryDirectory(prefix="erkenn-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER / "erkenn.tex", work / "erkenn.tex")
        latex(work, "erkenn", 3)
        shutil.copy(work / "erkenn.pdf", PAPER / "erkenn.pdf")
        title = PAPER / "erkenn-title.tex"
        if title.exists():
            shutil.copy(title, work / "erkenn-title.tex")
            latex(work, "erkenn-title", 1)
            shutil.copy(work / "erkenn-title.pdf", PAPER / "erkenn-title.pdf")
    print("wrote", PAPER / "erkenn.pdf")

if __name__ == "__main__":
    main()
