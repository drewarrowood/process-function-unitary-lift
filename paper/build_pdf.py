"""Build paper/lift.pdf from paper/lift.md (markdown-it-py + headless Chrome)."""
import pathlib, subprocess, tempfile, sys
here = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / "docs"))
from mdmath import LIFT_SUBS, render  # same Unicode-math converter as the web page
body = render((here / "lift.md").read_text(), LIFT_SUBS, "https://github.com/drewarrowood/process-function-unitary-lift")
body = body.replace('src="figs/', f'src="file://{here.parent}/docs/figs/')  # images live in docs/figs (relative for the site)
html = f"""<!doctype html><meta charset="utf-8"><title>Every process function lifts to a unitary process</title>
<style>body{{font-family:Georgia,serif;max-width:46em;margin:2em auto;line-height:1.45;font-size:11pt}}
pre{{background:#f4f4f4;padding:.5em;white-space:pre-wrap}} table{{border-collapse:collapse;font-size:9pt}} th,td{{border:1px solid #ccc;padding:1px 6px}} h1{{font-size:1.6em}} h2{{font-size:1.2em;margin-top:1.4em}} img{{max-width:100%}}</style>{body}"""
with tempfile.NamedTemporaryFile("w", suffix=".html", delete=False) as f:
    f.write(html)
subprocess.run(["google-chrome", "--headless=new", "--no-sandbox", "--disable-gpu", "--no-pdf-header-footer",
                f"--print-to-pdf={here/'lift.pdf'}", f"file://{f.name}"], check=True,
               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
print("wrote", here / "lift.pdf")
