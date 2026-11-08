"""Build the static site (no JS, Unicode math) from paper/lift.md and paper/graded.md.

Outputs docs/index.html (technical note), docs/graded.html (gentle version),
docs/foundations.html (Foundations of Physics draft), docs/synthese.html
(Synthese-style draft), docs/og.png and docs/og-graded.png.
Copies paper/foundations.pdf, paper/synthese.pdf, and paper/synthese-title.pdf
into docs/ without rewriting them.
"""
import pathlib, re, html, shutil, subprocess
from PIL import Image, ImageDraw, ImageFont
root = pathlib.Path(__file__).resolve().parent.parent
BASE = "https://drewarrowood.github.io/process-function-unitary-lift/"
REPO = "https://github.com/drewarrowood/process-function-unitary-lift"
CSS = """body{font-family:Georgia,'Times New Roman',serif;line-height:1.55;margin:0;padding:1rem;color:#111;background:#fff}
main{max-width:42rem;margin:0 auto} h1{font-size:1.6rem;line-height:1.25} h2{font-size:1.2rem;margin-top:2rem}
h3{font-size:1.05rem;margin-top:1.6rem} img{max-width:100%;height:auto}
pre{background:#f3f3f3;padding:.6rem;overflow-x:auto;font-size:.9rem;white-space:pre-wrap;word-break:break-word}
code{font-family:'DejaVu Sans Mono',Menlo,monospace;font-size:.9em} a{color:#0645ad;word-break:break-word}
li{margin:.3rem 0} footer{margin-top:3rem;font-size:.85rem;color:#555}
blockquote{margin:1rem 0;padding:.6rem .9rem;border-left:4px solid #9fb8d8;background:#f5f8fc}
blockquote p{margin:.4rem 0} nav.top{font-size:.92rem;margin:.2rem 0 1rem;padding:.5rem .7rem;background:#f3f3f3}
hr{border:0;border-top:1px solid #ddd;margin:2rem 0}
table{border-collapse:collapse;font-size:.9rem;display:block;overflow-x:auto} th,td{border:1px solid #ccc;padding:.2rem .5rem;text-align:right}"""

import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from mdmath import LIFT_SUBS, GRADED_SUBS, render as _render

def render(md, subs):
    return _render(md, subs, REPO)

FOOT = (
    f'Source: <a href="{REPO}">github.com/drewarrowood/process-function-unitary-lift</a> · '
    f'<a href="{BASE}lift.pdf">PDF (technical note)</a> · '
    f'<a href="{BASE}graded.pdf">PDF (gentle version)</a> · '
    f'<a href="{BASE}foundations.pdf">PDF (Foundations draft)</a> · '
    f'<a href="{BASE}synthese.pdf">PDF (Synthese draft)</a> · '
    f'<a href="{BASE}jphil.pdf">PDF (Journal of Philosophy draft)</a> · '
    f'<a href="{BASE}mind.pdf">PDF (Mind draft)</a> · '
    f'<a href="{BASE}pop.pdf">PDF (Philosophy of Physics draft)</a> · '
    f'<a href="{BASE}quantum.pdf">PDF (Quantum-style note)</a> · '
    f'<a href="{BASE}erkenn.pdf">PDF (Erkenntnis draft)</a> · '
    f'<a href="{BASE}philsci.pdf">PDF (Philosophy of Science draft)</a> · '
    f'<a href="{BASE}shps.pdf">PDF (Studies draft)</a> · '
    f'<a href="{BASE}">Technical note</a> · '
    f'<a href="{BASE}graded.html">Gentle version</a> · '
    f'<a href="{BASE}foundations.html">Foundations draft</a> · '
    f'<a href="{BASE}synthese.html">Synthese draft</a> · '
    f'<a href="{BASE}jphil.html">Journal of Philosophy draft</a> · '
    f'<a href="{BASE}mind.html">Mind draft</a> · '
    f'<a href="{BASE}pop.html">Philosophy of Physics draft</a> · '
    f'<a href="{BASE}quantum.html">Quantum-style note</a> · '
    f'<a href="{BASE}erkenn.html">Erkenntnis draft</a> · '
    f'<a href="{BASE}philsci.html">Philosophy of Science draft</a> · '
    f'<a href="{BASE}shps.html">Studies draft</a>'
)

def page(title, desc, url, og_image, nav, body):
    og = """<meta property="og:title" content="{t}"><meta property="og:description" content="{d}">
<meta property="og:type" content="article"><meta property="og:url" content="{u}">
<meta property="og:image" content="{i}"><meta property="og:image:width" content="1200">
<meta property="og:image:height" content="630"><meta property="og:image:type" content="image/png">
<meta name="twitter:card" content="summary_large_image"><meta name="twitter:title" content="{t}">
<meta name="twitter:description" content="{d}"><meta name="twitter:image" content="{i}">""".format(
        t=html.escape(title), d=html.escape(desc), u=url, i=og_image)
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<meta name="description" content="{html.escape(desc)}">
<link rel="canonical" href="{url}">
{og}
<style>
{CSS}
</style></head><body><main>
{nav}
{body}
<footer>{FOOT}</footer>
</main></body></html>
"""

def og_png(path, lines, formula, tagline):
    img = Image.new("RGB", (1200, 630), "#0f1b2d"); d = ImageDraw.Draw(img)
    F = "/usr/share/fonts/truetype/dejavu/"
    big = ImageFont.truetype(F + "DejaVuSerif-Bold.ttf", 64); mid = ImageFont.truetype(F + "DejaVuSans.ttf", 34)
    for n, line in enumerate(lines):
        d.text((70, 120 + 80 * n), line, font=big, fill="white")
    d.text((70, 330), formula, font=mid, fill="#9fd3ff")
    d.text((70, 400), tagline, font=mid, fill="#d0d0d0")
    d.text((70, 530), "Drew Arrowood · draft note", font=mid, fill="#a0a0a0")
    img.save(path)

# Technical note
TITLE = "Every process function lifts to a unitary process"
DESC = ("Draft note: for every classical process function, the source-sink permutation unitary "
        "is a valid unitary quantum process. Short proof, Stinespring validity argument, Lean 4 check.")
nav = (f'<nav class="top"><a href="{BASE}graded.html">Gentle version</a> · '
       f'<a href="{BASE}foundations.html">Foundations of Physics draft</a> · '
       f'<a href="{BASE}synthese.html">Synthese-style draft</a> · '
       f'<a href="{BASE}jphil.html">Journal of Philosophy draft</a> · '
       f'<a href="{BASE}mind.html">Mind draft</a> · '
       f'<a href="{BASE}pop.html">Philosophy of Physics draft</a> · '
       f'<a href="{BASE}quantum.html">Quantum-style note</a> · '
       f'<a href="{BASE}erkenn.html">Erkenntnis draft</a> · '
       f'<a href="{BASE}philsci.html">Philosophy of Science draft</a> · '
       f'<a href="{BASE}shps.html">Studies draft</a> '
       '(separate articles; this page remains the technical archive).</nav>')
(root / "docs/index.html").write_text(page(TITLE, DESC, BASE, BASE + "og.png", nav,
                                           render((root / "paper/lift.md").read_text(), LIFT_SUBS)))
og_png(root / "docs/og.png", ["Every process function", "lifts to a unitary process"],
       "U|o, e⟩ = |w(o) + e, o⟩   ⇒   M M† = 1", "Short proof · Stinespring validity · Lean 4 check")

# Gentle version
GTITLE = "Can every consistent time loop live in a reversible world? (Gentle version)"
GDESC = ("A graded, philosophically explained version of 'Every process function lifts to a unitary process': "
         "from time-travel stories to the main theorem, purification, random corners and the open conjecture.")
gnav = (f'<nav class="top">Gentle version. The technical source of truth is the <a href="{BASE}">technical note</a> '
        f'(<a href="{REPO}/blob/main/paper/lift.md">paper/lift.md</a>). '
        f'<a href="{BASE}foundations.html">Foundations of Physics draft</a> · '
        f'<a href="{BASE}synthese.html">Synthese-style draft</a> · '
        f'<a href="{BASE}jphil.html">Journal of Philosophy draft</a> · '
        f'<a href="{BASE}mind.html">Mind draft</a> · '
        f'<a href="{BASE}pop.html">Philosophy of Physics draft</a> · '
        f'<a href="{BASE}quantum.html">Quantum-style note</a> · '
        f'<a href="{BASE}erkenn.html">Erkenntnis draft</a> · '
        f'<a href="{BASE}philsci.html">Philosophy of Science draft</a> · '
        f'<a href="{BASE}shps.html">Studies draft</a>.</nav>')
(root / "docs/graded.html").write_text(page(GTITLE, GDESC, BASE + "graded.html", BASE + "og-graded.png", gnav,
                                            render((root / "paper/graded.md").read_text(), GRADED_SUBS)))
og_png(root / "docs/og-graded.png", ["Can every consistent loop", "live in a reversible world?"],
       "exactly one fixed point  ⇒  unitary lift", "Gentle version · stories → symbols → theorem → open problem")

# Glossary only (Appendix K plus the references it cites)
_lift = (root / "paper/lift.md").read_text()
_gl = _lift[_lift.index("## Appendix K. Glossary"):]
GLTITLE = "Glossary: Every process function lifts to a unitary process"
GLDESC = "Technical definitions of the main terms in the paper (Appendix K), with the references they cite."
glnav = (f'<nav class="top">Glossary only (Appendix K). Full paper: <a href="{BASE}">technical note</a> · '
         f'<a href="{BASE}graded.html">gentle version</a> · '
         f'<a href="{BASE}foundations.html">Foundations draft</a> · '
         f'<a href="{BASE}synthese.html">Synthese draft</a> · '
         f'<a href="{BASE}jphil.html">Journal of Philosophy draft</a> · '
         f'<a href="{BASE}mind.html">Mind draft</a> · '
         f'<a href="{BASE}pop.html">Philosophy of Physics draft</a> · '
         f'<a href="{BASE}quantum.html">Quantum-style note</a> · '
         f'<a href="{BASE}erkenn.html">Erkenntnis draft</a> · '
         f'<a href="{BASE}philsci.html">Philosophy of Science draft</a> · '
         f'<a href="{BASE}shps.html">Studies draft</a>.</nav>')
(root / "docs/glossary.html").write_text(page(GLTITLE, GLDESC, BASE + "glossary.html", BASE + "og.png", glnav,
                                              render(_gl, LIFT_SUBS)))

# Foundations of Physics draft (separate from the technical note and the gentle version).
# HTML is a reading copy of paper/foundations.tex. Numbered references are in the PDF.
_fn_body = subprocess.check_output(
    ["pandoc", str(root / "paper/foundations.tex"), "-t", "html", "--mathml", "--wrap=none"],
    text=True,
)
def _cite(m):
    keys = [k for k in m.group(1).split() if k]
    return "[" + "; ".join(keys) + "]" if keys else ""
_fn_body = re.sub(r'<span class="citation" data-cites="([^"]*)">\s*</span>', _cite, _fn_body)
# Pandoc's TeX reader rejects \Bigl in this one display. Keep the PDF untouched
# and show the same identity as Unicode so the reading copy has no raw TeX.
_STINE = (
    '<span class="math display">'
    'A<sub>k</sub>(ρ) = Tr<sub>E<sub>k</sub> E″<sub>k</sub></sub>'
    '(V<sub>k</sub>(ρ ⊗ |0⟩⟨0|) V<sub>k</sub>†).'
    '</span>'
)
_fn_body = re.sub(
    r'<span class="math display">\$\$A_k\(\\rho\).*?\$\$</span>',
    _STINE,
    _fn_body,
    count=1,
    flags=re.S,
)
FTITLE = "Classical consistency and quantum purification without a fixed causal order"
FDESC = ("Draft article in the style of Foundations of Physics: finite-alphabet unitary lift "
         "and a three-party purifiable classical process outside the process-function hull. Not submitted.")
fnav = (f'<nav class="top"><strong>Foundations of Physics draft.</strong> Not a journal submission. '
        f'Author declarations are pending. '
        f'<a href="{BASE}">Technical note</a> · '
        f'<a href="{BASE}graded.html">Gentle version</a> · '
        f'<a href="{BASE}synthese.html">Synthese-style draft</a> · '
        f'<a href="{BASE}foundations.pdf">PDF</a> · '
        f'<a href="{REPO}/blob/main/paper/foundations.tex">TeX source</a> · '
        f'<a href="{REPO}/blob/main/paper/foundations.md">Markdown source</a>.</nav>'
        '<h1>Classical consistency and quantum purification without a fixed causal order</h1>'
        '<p><strong>Draft for review. Not submitted.</strong> Drew Lamarr Arrowood. '
        'Affiliation, correspondence, ORCID, funding, and competing interests are pending confirmation. '
        'The typeset PDF is the reference copy; this HTML is a reading version of the same source.</p>')
(root / "docs/foundations.html").write_text(page(
    FTITLE, FDESC, BASE + "foundations.html", BASE + "og.png", fnav, _fn_body))
shutil.copyfile(root / "paper/foundations.pdf", root / "docs/foundations.pdf")

# Synthese-style draft. The review manuscript and the title page stay separate.
# docs/synthese.pdf is the review PDF, copied byte-for-byte. The HTML is a
# reading copy of that manuscript. It does not assert journal submission or
# that public hosting has anonymized the author.
_syn_body = subprocess.check_output(
    ["pandoc", str(root / "paper/synthese.tex"), "-t", "html", "--mathml", "--wrap=none"],
    text=True,
)
_syn_body = re.sub(r'<span class="citation" data-cites="([^"]*)">\s*</span>', _cite, _syn_body)
STITLE = "Consistency, reversibility, and the limits of causal-loop explanation"
SDESC = ("Draft article in the style of Synthese: local consistency without a fixed causal order, "
         "and why a reversible extension is not a time-travel claim. Not submitted.")
snav = (f'<nav class="top"><strong>Synthese-style draft.</strong> Not a journal submission. '
        f'The review text keeps the author line off this page. The separate title page is published '
        f'beside it, so anonymity is not claimed. Author declarations remain pending. '
        f'<a href="{BASE}">Technical note</a> · '
        f'<a href="{BASE}graded.html">Gentle version</a> · '
        f'<a href="{BASE}foundations.html">Foundations draft</a> · '
        f'<a href="{BASE}synthese.pdf">Review PDF</a> · '
        f'<a href="{BASE}synthese-title.pdf">Title page PDF</a> · '
        f'<a href="{REPO}/blob/main/paper/synthese.tex">TeX source</a> · '
        f'<a href="{REPO}/blob/main/paper/synthese.md">Markdown source</a> · '
        f'<a href="{REPO}/blob/main/paper/synthese-title.tex">Title-page source</a>.</nav>'
        f'<h1>{STITLE}</h1>'
        '<p><strong>Draft for review. Not submitted.</strong> '
        'This HTML follows the review manuscript. Affiliation, correspondence, ORCID, funding, '
        'and competing interests are pending confirmation on the title page. '
        'The review PDF is the reference copy.</p>')
(root / "docs/synthese.html").write_text(page(
    STITLE, SDESC, BASE + "synthese.html", BASE + "og.png", snav, _syn_body))
shutil.copyfile(root / "paper/synthese.pdf", root / "docs/synthese.pdf")
shutil.copyfile(root / "paper/synthese-title.pdf", root / "docs/synthese-title.pdf")

def _reading_page(stem, title, desc, banner, copies):
    body = subprocess.check_output(
        ["pandoc", str(root / "paper" / f"{stem}.tex"), "-t", "html", "--mathml", "--wrap=none"],
        text=True,
    )
    body = re.sub(r'<span class="citation" data-cites="([^"]*)">\s*</span>', _cite, body)
    (root / "docs" / f"{stem}.html").write_text(page(
        title, desc, BASE + f"{stem}.html", BASE + "og.png", banner + f"<h1>{html.escape(title)}</h1>", body))
    for src, dst in copies:
        shutil.copyfile(root / "paper" / src, root / "docs" / dst)

_cross = (f'<a href="{BASE}">Technical note</a> · '
          f'<a href="{BASE}graded.html">Gentle version</a> · '
          f'<a href="{BASE}foundations.html">Foundations draft</a> · '
          f'<a href="{BASE}synthese.html">Synthese draft</a> · '
          f'<a href="{BASE}jphil.html">Journal of Philosophy draft</a> · '
          f'<a href="{BASE}mind.html">Mind draft</a> · '
          f'<a href="{BASE}pop.html">Philosophy of Physics draft</a> · '
          f'<a href="{BASE}quantum.html">Quantum-style note</a> · '
          f'<a href="{BASE}erkenn.html">Erkenntnis draft</a> · '
          f'<a href="{BASE}philsci.html">Philosophy of Science draft</a> · '
          f'<a href="{BASE}shps.html">Studies draft</a>')

_reading_page(
    "jphil",
    "A Computer without a First Step?",
    "Draft in the style of the Journal of Philosophy. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Journal of Philosophy draft.</strong> Not a journal submission. '
    f'The review text omits the author line. The separate title page is public, so anonymity is not claimed. '
    f'{_cross} · <a href="{BASE}jphil.pdf">Review PDF</a> · '
    f'<a href="{BASE}jphil-title.pdf">Title page</a> · '
    f'<a href="{REPO}/blob/main/paper/jphil.tex">TeX</a>.</nav>',
    [("jphil.pdf", "jphil.pdf"), ("jphil-title.pdf", "jphil-title.pdf")],
)
_reading_page(
    "mind",
    "Independent Operations, Dependent Histories",
    "Draft in the style of Mind. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Mind draft.</strong> Not a journal submission. '
    f'Official initial placement of the assistance disclosure was not fully verified. '
    f'The declarations sheet is public, so anonymity is not claimed. '
    f'{_cross} · <a href="{BASE}mind.pdf">Review PDF</a> · '
    f'<a href="{BASE}mind-title.pdf">Declarations sheet</a> · '
    f'<a href="{REPO}/blob/main/paper/mind.tex">TeX</a>.</nav>',
    [("mind.pdf", "mind.pdf"), ("mind-title.pdf", "mind-title.pdf")],
)
_reading_page(
    "pop",
    "Operational validity is not a spacetime embedding",
    "Draft in the style of Philosophy of Physics. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Philosophy of Physics draft.</strong> Not a journal submission. '
    f'A public preprint can defeat anonymity, and related drafts are already public. '
    f'{_cross} · <a href="{BASE}pop.pdf">Review PDF</a> · '
    f'<a href="{BASE}pop-title.pdf">Declarations sheet</a> · '
    f'<a href="{REPO}/blob/main/paper/pop.tex">TeX</a>.</nav>',
    [("pop.pdf", "pop.pdf"), ("pop-title.pdf", "pop-title.pdf")],
)
_reading_page(
    "quantum",
    "The canonical unitary lift of a finite process function",
    "Technical draft in the style of Quantum. Not submitted and not uploaded to the arXiv.",
    f'<nav class="top"><strong>Quantum-style technical note.</strong> Not a journal submission and not an arXiv upload. '
    f'Single-blind style: the author line is on the PDF. Declarations are pending. '
    f'{_cross} · <a href="{BASE}quantum.pdf">PDF</a> · '
    f'<a href="{REPO}/blob/main/paper/quantum.tex">TeX</a>.</nav>',
    [("quantum.pdf", "quantum.pdf")],
)
_reading_page(
    "erkenn",
    "What universal consistency explains about composition",
    "Draft in the style of Erkenntnis. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Erkenntnis draft.</strong> Not a journal submission. '
    f'The review text omits the author line. The separate title page is public, so anonymity is not claimed. '
    f'{_cross} · <a href="{BASE}erkenn.pdf">Review PDF</a> · '
    f'<a href="{BASE}erkenn-title.pdf">Title page</a> · '
    f'<a href="{REPO}/blob/main/paper/erkenn.tex">TeX</a>.</nav>',
    [("erkenn.pdf", "erkenn.pdf"), ("erkenn-title.pdf", "erkenn-title.pdf")],
)
_reading_page(
    "philsci",
    "An admissible model is not yet an explanation",
    "Draft in the style of Philosophy of Science. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Philosophy of Science draft.</strong> Not a journal submission. '
    f'The review text omits the author line. A separate identity sheet is public, so anonymity is not claimed. '
    f'{_cross} · <a href="{BASE}philsci.pdf">Review PDF</a> · '
    f'<a href="{BASE}philsci-title.pdf">Identity sheet</a> · '
    f'<a href="{REPO}/blob/main/paper/philsci.tex">TeX</a>.</nav>',
    [("philsci.pdf", "philsci.pdf"), ("philsci-title.pdf", "philsci-title.pdf")],
)
_reading_page(
    "shps",
    "Succession is not a closed loop",
    "Draft in the style of Studies in History and Philosophy of Science. Not submitted. Anonymity is not claimed.",
    f'<nav class="top"><strong>Studies in History and Philosophy of Science draft.</strong> Not a journal submission. '
    f'The Elsevier guide for authors was not retrieved. The review text omits the author line as a precaution. '
    f'The identity sheet is public, so anonymity is not claimed. '
    f'{_cross} · <a href="{BASE}shps.pdf">Review PDF</a> · '
    f'<a href="{BASE}shps-title.pdf">Identity sheet</a> · '
    f'<a href="{REPO}/blob/main/paper/shps.tex">TeX</a>.</nav>',
    [("shps.pdf", "shps.pdf"), ("shps-title.pdf", "shps-title.pdf")],
)

(root / "docs/.nojekyll").write_text("")
print("ok")
