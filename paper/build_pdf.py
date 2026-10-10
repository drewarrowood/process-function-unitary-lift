"""Build paper/lift.pdf from paper/lift.md (markdown-it-py + headless Chrome)."""
import pathlib, subprocess, tempfile
from markdown_it import MarkdownIt
here = pathlib.Path(__file__).resolve().parent
body = MarkdownIt("commonmark").render((here / "lift.md").read_text())
html = f"""<!doctype html><meta charset="utf-8"><title>Every process function lifts to a unitary process</title>
<style>body{{font-family:Georgia,serif;max-width:46em;margin:2em auto;line-height:1.45;font-size:11pt}}
pre{{background:#f4f4f4;padding:.5em}} h1{{font-size:1.6em}} h2{{font-size:1.2em;margin-top:1.4em}}</style>{body}"""
with tempfile.NamedTemporaryFile("w", suffix=".html", delete=False) as f:
    f.write(html)
subprocess.run(["google-chrome", "--headless=new", "--no-sandbox", "--disable-gpu", "--no-pdf-header-footer",
                f"--print-to-pdf={here/'lift.pdf'}", f"file://{f.name}"], check=True,
               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
print("wrote", here / "lift.pdf")
