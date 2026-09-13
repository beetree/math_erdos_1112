#!/usr/bin/env python3
"""Check the short paper's explicit Lean declaration/file correspondence.

Each lean-correspondence directive must name a declaration displayed in the
formalization appendix and defined in its exact source file. This checks names
and locations, not theorem semantics or kernel verification; use lake build too.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEX = ROOT / "paper/erdos1112.tex"
text = TEX.read_text(encoding="utf-8")
appendix = text.split(r"\section{Formal verification and correspondence}", 1)[1]
visible = re.sub(r"(?<!\\)%[^\n]*", "", appendix).replace(r"\_", "_")
entries = re.findall(r"^% lean-correspondence: ([\w.']+) \| ([\w/.-]+\.lean)$", text, re.M)
errors = []
if not entries:
    errors.append("No correspondence entries found")
if len(entries) != len(set(entries)):
    errors.append("Duplicate correspondence entries")
for name, source in entries:
    path = ROOT / "lean" / source
    if not path.is_file():
        errors.append(f"Missing source: {source}")
        continue
    if rf"\texttt{{{name}}}" not in visible:
        errors.append(f"Declaration absent from printed appendix: {name}")
    lean = path.read_text(encoding="utf-8")
    # A mention in an import, comment, or proof body is not a declaration.
    lean = re.sub(r"/-.*?-/", "", lean, flags=re.S)
    lean = re.sub(r"--[^\n]*", "", lean)
    if not re.search(rf"\b(?:theorem|lemma|def|abbrev)\s+{re.escape(name)}(?=\s|\{{|\()", lean):
        errors.append(f"Declaration {name} not defined in {source}")
for error in errors:
    print(f"ERROR: {error}")
print(f"Correspondence: {len(entries)} declarations, {len(errors)} errors")
sys.exit(bool(errors))
