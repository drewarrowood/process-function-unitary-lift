"""Markdown -> HTML with Unicode math, shared by docs/build_site.py and paper/build_pdf.py.

lift.md writes math in ASCII: tensor products as ' (x) ' (spaced) or a prefix '(x)_k', kets as |o>,
daggers as ^dagger, subscripts as x_k or x_{...}. Function applications such as f(x) must stay as they are.
"""
import re
from markdown_it import MarkdownIt

US = "\ue000"  # stands in for '_' while markdown parses, so subscripts never become <em> emphasis

# Applied to the rendered HTML of lift.md, in order.
LIFT_SUBS = [
    (r"\^dagger", "†"), (r"\^†", "†"),
    # Tensor product: only the spaced infix ' (x) ' and the prefix product '(x)_k' after a space.
    # A function application like f(x) or f_k(x) has no space before '(x)' and is left alone.
    (r"(?<=\s)\(x\)(?=\s|_)", "⊗"),
    (r"&lt;=&gt;", "⇔"), (r"=&gt;", "⇒"), (r"-&gt;", "→"), (r"&gt;=", "≥"), (r"&lt;=", "≤"), (r"!=", "≠"),
    (r"&lt;&lt;U\|", "⟨⟨U|"), (r"\|U&gt;&gt;", "|U⟩⟩"),
    (r"\|([^|&\n<]{1,24}?)&gt;", r"|\1⟩"), (r"&lt;([^|&\n<]{1,24}?)\|", r"⟨\1|"),
    (r"\^\{([^}<]{1,12})\}", r"<sup>\1</sup>"), (r"\^(-?[0-9]+)\b", r"<sup>\1</sup>"),
    (r"\^(⊥|[A-Z])(?![A-Za-z])", r"<sup>\1</sup>"),
    (r"\bprod_k\b", "∏<sub>k</sub>"),
    (r"\bsum_\{([^}<]{1,20})\}", r"∑<sub>\1</sub>"), (r"\bsum_([a-z]+)\b", r"∑<sub>\1</sub>"),
    (r"(⊗|Σ|⊕|\))_([a-z])\b", r"\1<sub>\2</sub>"), (r"\b1_([A-Z])\b", r"1<sub>\1</sub>"),
    (r"\b(Tr|id|Pi|delta)_\{([^}<]{1,16})\}", r"\1<sub>\2</sub>"),
    (r"\b(Tr|id|Pi|delta)_([A-Za-z0-9]+)\b", r"\1<sub>\2</sub>"),
    (r"(⟩|\|)_\{([^}<]{1,16})\}", r"\1<sub>\2</sub>"), (r"(⟩|\|)_([A-Za-z]+)\b", r"\1<sub>\2</sub>"),
    (r"\b([A-Za-zEGVSWpfw]'{0,2})_\{([^}<]{1,12})\}", r"\1<sub>\2</sub>"),
    (r"\b([A-Za-z]'{0,2})_([A-Za-z0-9]+'?)(?![A-Za-z0-9_])", r"\1<sub>\2</sub>"),
]
# graded.md is already written in Unicode; only turn x_y / x_{yz} into subscripts.
GRADED_SUBS = [
    (r"(?<![\w/.\-])([A-Za-zΠ])_\{([^}<]{1,12})\}", r"\1<sub>\2</sub>"),
    (r"(?<![\w/.\-])([A-Za-zΠΣ1])_([A-Za-z0-9λ]+)(?![\w])", r"\1<sub>\2</sub>"),
    (r"⟩_([A-Za-z0-9]+)(?![\w])", r"⟩<sub>\1</sub>"),
]

def render(md, subs, repo=None):
    if repo:
        md = md.replace("(lean/", f"({repo}/blob/main/lean/")
    md = md.replace("_", US)
    body = MarkdownIt("commonmark").enable("table").render(md).replace(US, "_")
    # Rewrite only text between tags, so attribute values such as hrefs are never altered.
    def conv(text):
        for a, b in subs:
            text = re.sub(a, b, text)
        return text
    return "".join(p if p.startswith("<") else conv(p) for p in re.split(r"(<[^>]+>)", body))
