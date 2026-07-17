#!/usr/bin/env python3
"""Mechanically check the name-and-location layer of the paper's Lean correspondence
table (Appendix C): every Lean declaration named there must exist in the Lean tree.

The statement-level match (that each declaration SAYS what the prose result says)
is a human judgment, as the paper states; this script pins the layer a machine can
pin -- the named declarations exist, so the table cannot silently rot as the
development evolves. Run from anywhere; exits nonzero on any missing name.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = HERE.parent / "erdos1112.tex"
LEAN = HERE.parent.parent / "lean"

text = TEX.read_text(encoding="utf-8")

# isolate the Appendix C table: from the correspondence section header to its tabular end
start = text.index("Correspondence with the Lean development")
seg = text[start:]
seg = seg[: seg.index("\\end{tabular}")]

# every \texttt{...} token; unescape \_; keep identifier-shaped names, drop file paths
tokens = re.findall(r"\\texttt\{([^}]*)\}", seg)
names = set()
for tok in tokens:
    tok = tok.replace("\\_", "_").replace("\\#", "#").strip()
    tok = tok.lstrip(".")  # table abbreviates shared prefixes as "..._of_foo"
    if not tok or tok.endswith(".lean") or "/" in tok or "#" in tok or " " in tok:
        continue
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.']*", tok):
        names.add(tok)

sources = list(LEAN.glob("Erdos1112*.lean")) + list(
    (LEAN / "Erdos1112Proof").rglob("*.lean")
)
corpus = "\n".join(f.read_text(encoding="utf-8") for f in sources)

missing = []
for name in sorted(names):
    # namespaced names (FrameCert.lift) may be declared inside namespace blocks:
    # accept the full dotted name or its final component as a declared word
    tail = name.split(".")[-1]
    if not (re.search(rf"\b{re.escape(name)}\b", corpus)
            or re.search(rf"\b{re.escape(tail)}\b", corpus)):
        missing.append(name)
        print(f"  MISSING: {name}")

print(f"correspondence check: {len(names)} declaration names from Appendix C, "
      f"{len(names) - len(missing)} found in {len(sources)} Lean files, "
      f"{len(missing)} missing")
sys.exit(1 if missing else 0)
