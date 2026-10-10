"""Build docs/index.html (static, no JS, Unicode math) and docs/og.png from paper/lift.md."""
import pathlib, re, html
from markdown_it import MarkdownIt
from PIL import Image, ImageDraw, ImageFont
root = pathlib.Path(__file__).resolve().parent.parent
URL = "https://drewarrowood.github.io/process-function-unitary-lift/"
TITLE = "Every process function lifts to a unitary process"
DESC = ("Draft note: for every classical process function, the source-sink permutation unitary "
        "is a valid unitary quantum process. Short proof, Stinespring validity argument, Lean 4 check.")
md = (root / "paper/lift.md").read_text()
md = md.replace("(lean/", "(https://github.com/drewarrowood/process-function-unitary-lift/blob/main/lean/")
body = MarkdownIt("commonmark").render(md)
subs = [(r"\^dagger", "†"), (r"\(x\)", "⊗"), (r"-&gt;", "→"), (r"&gt;=", "≥"), (r"!=", "≠"),
        (r"&lt;&lt;U\|", "⟨⟨U|"), (r"\|U&gt;&gt;", "|U⟩⟩"),
        (r"\|([^|&\n<]{1,24}?)&gt;", r"|\1⟩"), (r"&lt;([^|&\n<]{1,24}?)\|", r"⟨\1|"),
        (r"\bprod_k\b", "∏<sub>k</sub>"), (r"\bsum_\{?([a-z]+(?:, [a-z_]+)?)\}?", r"∑<sub>\1</sub>"),
        (r"\b([A-Za-zEGVSWpfw]'{0,2})_\{([^}<]{1,12})\}", r"\1<sub>\2</sub>"),
        (r"\b([A-Za-z]'{0,2})_([A-Za-z0-9]'?)(?![A-Za-z0-9_])", r"\1<sub>\2</sub>")]
for a, b in subs:
    body = re.sub(a, b, body)
og = """<meta property="og:title" content="{t}"><meta property="og:description" content="{d}">
<meta property="og:type" content="article"><meta property="og:url" content="{u}">
<meta property="og:image" content="{u}og.png"><meta property="og:image:width" content="1200">
<meta property="og:image:height" content="630"><meta property="og:image:type" content="image/png">
<meta name="twitter:card" content="summary_large_image"><meta name="twitter:title" content="{t}">
<meta name="twitter:description" content="{d}"><meta name="twitter:image" content="{u}og.png">""".format(
    t=html.escape(TITLE), d=html.escape(DESC), u=URL)
page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(TITLE)}</title>
<meta name="description" content="{html.escape(DESC)}">
<link rel="canonical" href="{URL}">
{og}
<style>
body{{font-family:Georgia,'Times New Roman',serif;line-height:1.55;margin:0;padding:1rem;color:#111;background:#fff}}
main{{max-width:42rem;margin:0 auto}} h1{{font-size:1.6rem;line-height:1.25}} h2{{font-size:1.2rem;margin-top:2rem}}
pre{{background:#f3f3f3;padding:.6rem;overflow-x:auto;font-size:.9rem;white-space:pre-wrap;word-break:break-word}}
code{{font-family:'DejaVu Sans Mono',Menlo,monospace;font-size:.9em}} a{{color:#0645ad;word-break:break-word}}
li{{margin:.3rem 0}} footer{{margin-top:3rem;font-size:.85rem;color:#555}}
</style></head><body><main>
{body}
<footer>Source: <a href="https://github.com/drewarrowood/process-function-unitary-lift">github.com/drewarrowood/process-function-unitary-lift</a> · <a href="https://github.com/drewarrowood/process-function-unitary-lift/raw/main/paper/lift.pdf">PDF</a></footer>
</main></body></html>
"""
(root / "docs/index.html").write_text(page)
(root / "docs/.nojekyll").write_text("")
img = Image.new("RGB", (1200, 630), "#0f1b2d"); d = ImageDraw.Draw(img)
F = "/usr/share/fonts/truetype/dejavu/"
big = ImageFont.truetype(F + "DejaVuSerif-Bold.ttf", 64); mid = ImageFont.truetype(F + "DejaVuSans.ttf", 34)
d.text((70, 120), "Every process function", font=big, fill="white")
d.text((70, 200), "lifts to a unitary process", font=big, fill="white")
d.text((70, 330), "U|o, e⟩ = |w(o) + e, o⟩   ⇒   M M† = 1", font=mid, fill="#9fd3ff")
d.text((70, 400), "Short proof · Stinespring validity · Lean 4 check", font=mid, fill="#d0d0d0")
d.text((70, 530), "Drew Arrowood · draft note", font=mid, fill="#a0a0a0")
img.save(root / "docs/og.png")
print("ok")
