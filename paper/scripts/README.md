# Python verification harnesses

Two independent Python 3 programs (standard library only, no dependencies) that corroborate the
**finite layer** of the proof — they cover every hard-core triple with `max(G) ≤ 120` by the multiset
that the paper's route D/P/L/E/T/B designates (Case T by the applicable variant of Construction T),
verify each witness exactly in integer arithmetic, and validate the certificate tables of Appendix B.
They check the finite content only; the asymptotic lemmas are proved in the paper and formalized in
Lean. Both programs **fail closed**: any invalid witness, missing class, or count differing from the
expected totals (83,251 triples; 172 Table-A rows; 178 Table-B classes; zero failures) exits nonzero.

## `sharp6_final.py` — the constructive harness

Covers each triple by its designated branch, consuming the canonical certificate tables
(`../data/table-A.csv`, `../data/table-B.csv`) where the route calls for them:

```console
$ python3 sharp6_final.py 120
hard core M<=120: 83251 triples
branch counts: {'B': 1987, 'D': 2392, 'E': 71421, 'L': 1420, 'P': 2605, 'T': 3254, 'T-table': 172}
Table-A rows used: 172 (canonical table has 172)
DESIGNATED-BRANCH FAILURES (must be 0): 0
$ echo $?
0
```

## `sharp_referee_check.py` — the independent re-check

A re-implementation that shares no code with the first: it rebuilds each designated witness from the
lemma statements alone (no auxiliary searches), reports the same branch counts, re-validates both
certificate tables (including base-minimality and class-completeness), re-runs the `a ≤ 3000` Case-T
scan — whose failure set must equal Table A exactly, with the tail margin recomputed in exact
rational arithmetic (minimum 993 at `a = 3000`) — walks the λ-lift chains, verifies the Case-P reach
inequalities, and re-checks the machinery lemmas by brute force. It reads the certificate tables from
`probes2/sharp_tables.txt`, generated from the canonical data:

```console
$ python3 make_tables_file.py            # writes probes2/sharp_tables.txt from ../data/certificate-data.md
$ python3 sharp_referee_check.py 120
...
FATAL/CONSTRUCTION FAILURES: 0
WARNINGS (write-up/bookkeeping): 0
$ echo $?
0
```

## Notes

- The canonical certificate data is [`../data/certificate-data.md`](../data/certificate-data.md);
  the machine-readable exports are in [`../data/`](../data). The Lean development transcribes the
  same rows and the kernel decides them, so the finite layer is checked three ways: these harnesses,
  the paper's re-verifier (`../gen-tables.py`), and the Lean kernel.
- Both harnesses implement the paper's **current** route (variant A / base form in Case T; the
  uniform pair-frame in Case P). Earlier releases shipped harnesses implementing a retired
  variant-B Case-T route with a 158-row exceptional set; that route, and the 158-vs-172 warning it
  produced, are gone.
- All ceiling divisions are exact integer arithmetic (`cdiv`); no floating point is used anywhere.
- Continuous integration (`.github/workflows/verify.yml`) runs both programs to `M = 120` on every
  push, alongside the Lean build and axiom audit.
- `check_correspondence.py` verifies that every Lean declaration named in the paper's Appendix C
  exists in the Lean tree.
- `probes2/` is generated and git-ignored.
