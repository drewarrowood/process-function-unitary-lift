#!/usr/bin/env python3
"""Rebuild docs/lift.pdf and docs/graded.pdf from the current markdown sources.

The published PDFs are LuaLaTeX via pandoc (letter paper, 11pt, 1in margins,
STIX Two Text / STIX Two Math, DejaVu Sans Mono). Appendix M is the six-column
Lean-results table. It is set in landscape, with a narrower axioms column, so
that column wraps inside the page instead of running into the margin.

Requires: pandoc, lualatex, pdflscape (texlive), and the fonts
STIX Two Text, STIX Two Math, DejaVu Sans, DejaVu Sans Mono.
The figure paper/lift.md and paper/graded.md call figs/fourterms.png lives in
docs/figs/.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"
def _cmap(path: Path) -> set[int]:
    data = path.read_bytes()
    n = int.from_bytes(data[4:6], "big")
    off = 12
    cmap_off = None
    for _ in range(n):
        tag = data[off : off + 4]
        toff = int.from_bytes(data[off + 8 : off + 12], "big")
        if tag == b"cmap":
            cmap_off = toff
            break
        off += 16
    if cmap_off is None:
        return set()
    chars: set[int] = set()
    num = int.from_bytes(data[cmap_off + 2 : cmap_off + 4], "big")
    for i in range(num):
        base = cmap_off + 4 + i * 8
        plat = int.from_bytes(data[base : base + 2], "big")
        sub = cmap_off + int.from_bytes(data[base + 4 : base + 8], "big")
        fmt = int.from_bytes(data[sub : sub + 2], "big")
        if plat not in (0, 3):
            continue
        if fmt == 12:
            ngrp = int.from_bytes(data[sub + 12 : sub + 16], "big")
            p = sub + 16
            for _g in range(ngrp):
                s = int.from_bytes(data[p : p + 4], "big")
                e = int.from_bytes(data[p + 4 : p + 8], "big")
                chars.update(range(s, e + 1))
                p += 12
        elif fmt == 4:
            seg = int.from_bytes(data[sub + 6 : sub + 8], "big") // 2
            end = sub + 14
            ends = [int.from_bytes(data[end + 2 * j : end + 2 * j + 2], "big") for j in range(seg)]
            start_pos = end + 2 * seg + 2
            starts = [
                int.from_bytes(data[start_pos + 2 * j : start_pos + 2 * j + 2], "big")
                for j in range(seg)
            ]
            for j in range(seg):
                if ends[j] == 0xFFFF:
                    continue
                chars.update(range(starts[j], ends[j] + 1))
    return chars


def _font(*names: str) -> Path | None:
    roots = [
        Path.home() / ".local/share/fonts",
        Path("/usr/share/fonts"),
        Path("/usr/share/texmf/fonts"),
    ]
    for root in roots:
        if not root.exists():
            continue
        for name in names:
            hits = list(root.rglob(name))
            if hits:
                return hits[0]
    return None


def make_header() -> str:
    """Preamble: landscape tables, breakable \\texttt, and glyph fallbacks.

    STIX Two Text has no operators and no fraktur. Those characters are drawn
    from STIX Two Math, then DejaVu Sans, so Greek and the axioms column match
    the previous PDFs.
    """
    text = _cmap(_font("STIXTwoText-Regular.otf"))
    math = _cmap(_font("STIXTwoMath-Regular.otf"))
    deja = _cmap(_font("DejaVuSans.ttf"))
    mono = _cmap(_font("DejaVuSansMono.ttf"))
    used: set[int] = set()
    in_code: set[int] = set()
    for md in (ROOT / "paper" / "lift.md", ROOT / "paper" / "graded.md"):
        raw = md.read_text()
        used.update(ord(ch) for ch in raw)
        for span in re.findall(r"`([^`]+)`", raw):
            in_code.update(ord(ch) for ch in span if ord(ch) > 127)
    lines = [
        r"\usepackage{pdflscape}",
        r"\usepackage{newunicodechar}",
        r"\newfontfamily\pfulmathsym{STIX Two Math}",
        r"\newfontfamily\pfuldeja{DejaVu Sans}",
        r"% Break Lean names inside \texttt after underscores (Appendix M).",
        r"\renewcommand{\texttt}[1]{\begingroup\ttfamily",
        r"  \def\_{\textunderscore\discretionary{}{}{}}#1\endgroup}",
    ]
    for cp in sorted(
        c
        for c in used
        if c > 127 and (c not in text or (c in in_code and c not in mono))
    ):
        if cp in math:
            fam = r"\pfulmathsym"
        elif cp in deja:
            fam = r"\pfuldeja"
        else:
            raise SystemExit(f"no font for U+{cp:04X} {chr(cp)}")
        lines.append(rf"\newunicodechar{{{chr(cp)}}}{{{{{fam} \symbol{{{cp}}}}}}}")
    return "\n".join(lines) + "\n"

# Fractions of the landscape text width. They sum to 1.
# The axioms column is wide enough for "propext,choice," / "Quot.sound".
AXIOM_WIDTHS = ("0.07", "0.22", "0.12", "0.24", "0.19", "0.16")


def preprocess(md: str) -> str:
    """Turn HTML anchors into pandoc spans so Appendix M labels are targets."""
    return re.sub(r'<a id="([^"]+)"></a>', r"[]{#\1}", md)


def landscape_axioms(tex: str) -> str:
    """Put the Appendix M longtable on landscape pages with tuned widths."""
    begin = r"\begin{longtable}"
    end = r"\end{longtable}"
    out = []
    i = 0
    while True:
        j = tex.find(begin, i)
        if j < 0:
            out.append(tex[i:])
            break
        out.append(tex[i:j])
        k = tex.find(end, j)
        if k < 0:
            out.append(tex[j:])
            break
        k2 = k + len(end)
        block = tex[j:k2]
        head = block.split(r"\toprule", 1)[0]
        if head.count(r"\real{") == 6 and "Axioms" in block[:4000]:
            n = {"i": 0}

            def repl(m: re.Match[str]) -> str:
                w = AXIOM_WIDTHS[n["i"]]
                n["i"] += 1
                return m.group(1) + w + m.group(2)

            block = re.sub(r"(\\real\{)[0-9.]+(\})", repl, block)
            if n["i"] != 6:
                raise SystemExit(f"expected 6 column widths, rewrote {n['i']}")
            block = "\\begin{landscape}\n\\small\n" + block + "\n\\end{landscape}\n"
        out.append(block)
        i = k2
    return "".join(out)


def build_one(md_path: Path, pdf_name: str, work: Path) -> None:
    raw = preprocess(md_path.read_text())
    src = work / (md_path.stem + ".md")
    src.write_text(raw)
    tex_path = work / (md_path.stem + ".tex")
    header = work / "header.tex"
    header.write_text(make_header())
    cmd = [
        "pandoc",
        str(src),
        "-o",
        str(tex_path),
        "--from",
        "markdown+tex_math_dollars+raw_html",
        "--to",
        "latex",
        "--standalone",
        "--toc",
        "--pdf-engine=lualatex",
        "-V",
        "fontsize=11pt",
        "-V",
        "geometry:margin=1in",
        "-V",
        "mainfont=STIX Two Text",
        "-V",
        "sansfont=DejaVu Sans",
        "-V",
        "monofont=DejaVu Sans Mono",
        "-V",
        "mathfont=STIX Two Math",
        "-H",
        str(header),
        "--resource-path",
        os.pathsep.join([str(DOCS), str(ROOT / "paper"), str(ROOT)]),
    ]
    subprocess.run(cmd, check=True)
    fig = DOCS / "figs" / "fourterms.png"
    tex = tex_path.read_text().replace("figs/fourterms.png", fig.as_posix())
    tex = landscape_axioms(tex)
    tex_path.write_text(tex)
    for _ in range(2):
        subprocess.run(
            ["lualatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=work,
            check=True,
        )
    shutil.copyfile(work / (md_path.stem + ".pdf"), DOCS / pdf_name)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="pful-pdf-") as tmp:
        work = Path(tmp)
        # Separate directories so the two jobs do not clobber aux files.
        lift = work / "lift"
        graded = work / "graded"
        lift.mkdir()
        graded.mkdir()
        build_one(ROOT / "paper" / "lift.md", "lift.pdf", lift)
        build_one(ROOT / "paper" / "graded.md", "graded.pdf", graded)
    print("wrote", DOCS / "lift.pdf")
    print("wrote", DOCS / "graded.pdf")


if __name__ == "__main__":
    main()
