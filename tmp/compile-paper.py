#!/usr/bin/env python3
"""Assemble the per-part paper sources in ../proof/ into a single Markdown file.

Generator for the combined single-file paper, `proof/erdos1112-paper.md` — a
committed, generated artifact (the whole paper in one file). The canonical
sources are the per-part files in proof/; this only concatenates them.

Usage:
    python3 tmp/compile-paper.py [OUTPUT.md]      # default: proof/erdos1112-paper.md

For each source part this script strips the navigation breadcrumb (top line) and
the footer (trailing '---' + nav), injects an HTML anchor `<a id="sec-<stem>">`
for in-document cross-references, and rewrites sibling `foo.md[#frag]` links to
`#sec-foo`. Links of the form `../lean/...` and `../README.md` are left as-is:
the output lives in proof/, at the same depth as tmp/, so they resolve unchanged.
A short table of contents is prepended. Re-run after editing anything in proof/.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))          # .../tmp
REPO = os.path.dirname(HERE)                               # repo root
PROOF = os.path.join(REPO, "proof")

# Reading order (matches the manuscript: overview, Parts I-IV, appendices).
ORDER = [
    "00-overview",
    "01-existence",
    "02-nonexistence",
    "03-sharp",
    "04-assembly",
    "appendix-A-verification",
    "attribution-and-status",
    "appendix-B-tables",
    "appendix-C-scripts",
    "appendix-D-lean",
    "statement-faithfulness",
]
STEMS = set(ORDER)
LINK = re.compile(r"\]\(([^)]+)\)")


def strip_nav(text):
    """Remove the leading breadcrumb line and the trailing '---' + nav footer."""
    lines = text.split("\n")
    if lines and lines[0].startswith("*Erd") and lines[0].rstrip().endswith("*"):
        lines = lines[1:]
        while lines and lines[0].strip() == "":
            lines = lines[1:]
    hr = [i for i, l in enumerate(lines) if l.strip() == "---"]
    if hr:
        lines = lines[: hr[-1]]
    while lines and lines[-1].strip() == "":
        lines = lines[:-1]
    return "\n".join(lines)


def rewrite_link(target):
    base, sep, frag = target.partition("#")
    # sibling proof part -> in-document anchor; '../…' links resolve as-is from tmp/
    if not base.startswith("../") and base.endswith(".md"):
        stem = os.path.basename(base)[:-3]
        if stem in STEMS:
            return "](#sec-" + stem + ")"
    return "](" + target + ")"


def first_heading(body):
    for l in body.split("\n"):
        s = l.lstrip()
        if s.startswith("#"):
            return s.lstrip("#").strip()
    return None


def main():
    out_path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(PROOF, "erdos1112-paper.md")

    sections = []
    for stem in ORDER:
        with open(os.path.join(PROOF, stem + ".md"), encoding="utf-8") as fh:
            body = LINK.sub(lambda m: rewrite_link(m.group(1)), strip_nav(fh.read()))
        sections.append((stem, body, first_heading(body) or stem))

    out = [
        "<!-- AUTO-GENERATED — do not edit directly. -->",
        "<!-- Assembled from proof/*.md by tmp/compile-paper.py; edit those sources and re-run. -->",
        "",
        "**Contents**",
        "",
    ]
    out += ["- [%s](#sec-%s)" % (title, stem) for stem, _, title in sections]
    out.append("")
    for stem, body, _ in sections:
        out.append('<a id="sec-%s"></a>' % stem)
        out.append("")
        out.append(body)
        out.append("")

    combined = "\n".join(out).rstrip() + "\n"
    with open(out_path, "w", encoding="utf-8") as fh:
        fh.write(combined)
    print("wrote %s  (%d sections, %d bytes)" % (os.path.relpath(out_path, REPO),
                                                 len(sections), len(combined.encode("utf-8"))))


if __name__ == "__main__":
    main()
