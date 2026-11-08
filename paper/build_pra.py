#!/usr/bin/env python3
"""Build paper/pra.pdf with REVTeX 4.2."""
from __future__ import annotations
import shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

def run(cmd, work):
    env = dict(**{k:v for k,v in __import__("os").environ.items()})
    extra = str(PAPER/"revtex")
    env["TEXINPUTS"] = extra + ":" + env.get("TEXINPUTS","")
    env["BSTINPUTS"] = extra + ":" + env.get("BSTINPUTS","")
    subprocess.run(cmd, cwd=work, check=True, env=env)

def main():
    with tempfile.TemporaryDirectory(prefix="pra-pdf-") as tmp:
        work = Path(tmp)
        shutil.copy(PAPER/"pra.tex", work/"pra.tex")
        shutil.copy(PAPER/"pra.bib", work/"pra.bib")
        run(["pdflatex","-interaction=nonstopmode","-halt-on-error","pra.tex"], work)
        run(["bibtex","pra"], work)
        run(["pdflatex","-interaction=nonstopmode","-halt-on-error","pra.tex"], work)
        run(["pdflatex","-interaction=nonstopmode","-halt-on-error","pra.tex"], work)
        shutil.copy(work/"pra.pdf", PAPER/"pra.pdf")
    print("wrote", PAPER/"pra.pdf")

if __name__ == "__main__":
    main()
