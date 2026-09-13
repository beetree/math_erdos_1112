#!/usr/bin/env python3
"""Reject missing audit lines and any axiom outside Lean's standard foundations."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
audit_source = (root / "lean/Erdos1112Proof/AxiomsCheck.lean").read_text()
expected = set(re.findall(r"^#print axioms (\S+)$", audit_source, re.M))
text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
actual = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    actual[name] = {a.strip() for a in axioms.split(',') if a.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
errors = [f"Missing audit: {name}" for name in sorted(expected - actual.keys())]
for name, axioms in actual.items():
    if axioms - allowed:
        errors.append(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
for error in errors:
    print(error)
print(f"Axiom audit: {len(expected)} expected declarations, {len(errors)} errors")
sys.exit(bool(errors))
