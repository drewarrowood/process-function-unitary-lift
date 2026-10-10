"""Build the static site (no JS, Unicode math) from paper/lift.md and paper/graded.md.

Outputs docs/index.html (technical note), docs/graded.html (gentle version), docs/og.png and docs/og-graded.png.
"""
import pathlib, re, html
from PIL import Image, ImageDraw, ImageFont
root = pathlib.Path(__file__).resolve().parent.parent
BASE = "https://drewarrowood.github.io/process-function-unitary-lift/"
REPO = "https://github.com/drewarrowood/process-function-unitary-lift"
CSS = """body{font-family:Georgia,'Times New Roman',serif;line-height:1.55;margin:0;padding:1rem;color:#111;background:#fff}
main{max-width:42rem;margin:0 auto} h1{font-size:1.6rem;line-height:1.25} h2{font-size:1.2rem;margin-top:2rem}
h3{font-size:1.05rem;margin-top:1.6rem}
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
<footer>Source: <a href="{REPO}">github.com/drewarrowood/process-function-unitary-lift</a> · <a href="{REPO}/raw/main/paper/lift.pdf">PDF</a> · <a href="{BASE}">Technical note</a> · <a href="{BASE}graded.html">Gentle version</a></footer>
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
nav = (f'<nav class="top"><strong>New:</strong> <a href="{BASE}graded.html">Gentle version</a>, '
       'a graded walk-through that starts with time-travel stories and explains the philosophy behind every symbol.</nav>')
(root / "docs/index.html").write_text(page(TITLE, DESC, BASE, BASE + "og.png", nav,
                                           render((root / "paper/lift.md").read_text(), LIFT_SUBS)))
og_png(root / "docs/og.png", ["Every process function", "lifts to a unitary process"],
       "U|o, e⟩ = |w(o) + e, o⟩   ⇒   M M† = 1", "Short proof · Stinespring validity · Lean 4 check")

# Gentle version
GTITLE = "Can every consistent time loop live in a reversible world? (Gentle version)"
GDESC = ("A graded, philosophically explained version of 'Every process function lifts to a unitary process': "
         "from time-travel stories to the main theorem, purification, random corners and the open conjecture.")
gnav = (f'<nav class="top">Gentle version. The technical source of truth is the <a href="{BASE}">technical note</a> '
        f'(<a href="{REPO}/blob/main/paper/lift.md">paper/lift.md</a>).</nav>')
(root / "docs/graded.html").write_text(page(GTITLE, GDESC, BASE + "graded.html", BASE + "og-graded.png", gnav,
                                            render((root / "paper/graded.md").read_text(), GRADED_SUBS)))
og_png(root / "docs/og-graded.png", ["Can every consistent loop", "live in a reversible world?"],
       "exactly one fixed point  ⇒  unitary lift", "Gentle version · stories → symbols → theorem → open problem")

(root / "docs/.nojekyll").write_text("")
print("ok")
