# Python verification harnesses

Two independent Python 3 programs (standard library only, no dependencies) that corroborate the
**finite layer** of the proof — the certificate tables of Appendix B and the exhaustion of the
hard-core decision tree. They check the finite content only; the asymptotic lemmas are proved in the
paper and formalized in Lean. See Appendix A of the paper for what these verify and why.

## `sharp6_final.py` — the constructive harness

Runs the decision tree over every hard-core triple with `max(G) ≤ Mmax`, covering each by its
designated branch with an exactly verified multiset, and prints the branch counts and the failure
total (which must be 0). Runs standalone:

```console
$ python3 sharp6_final.py 120
hard core M<=120: 83251 triples
branch usage: {...}
DESIGNATED-BRANCH FAILURES (must be 0): 0
```

## `sharp_referee_check.py` — the independent re-check

A re-implementation that shares no code with `sharp6_final.py`: it rebuilds each witness from the
lemma statements, re-validates both certificate tables, walks the λ-lift chains, and re-checks the
machinery lemmas by brute force. It reads the certificate tables from `probes2/sharp_tables.txt`, so
generate that first from the canonical data:

```console
$ python3 make_tables_file.py            # writes probes2/sharp_tables.txt from ../data/certificate-data.md
$ python3 sharp_referee_check.py 120
...
FATAL/CONSTRUCTION FAILURES: 0
WARNINGS (write-up/bookkeeping): 0
```

## Notes

- The canonical certificate data is [`../data/certificate-data.md`](../data/certificate-data.md);
  the machine-readable exports are in [`../data/`](../data). The Lean development transcribes the
  same rows independently and the kernel decides them (`lean/…/Sharp/TablesData.lean`), so the finite
  layer is checked three ways: these harnesses, the paper's re-verifier (`../gen-tables.py`), and the
  Lean kernel.
- The harness branch labels (`P-small`, `TABLE-line/box`, …) are internal to the harnesses' own case
  split, which predates the paper's canonical D/P/L/E/T/B routing; the two agree on the finite layer,
  which is what these corroborate.
- **Route note (158 vs 172).** These harnesses implement the older *variant-B* Case-T route, whose
  exceptional set is 158 rows; the paper adopted the *merge-robust* route (172 rows, Appendix B),
  which avoids Lemma 4.4(c). Both correctly certify the finite layer — the 14-row difference is the
  documented route choice (paper §6, reconciliation table). Consequently `sharp_referee_check.py`,
  fed the canonical 172-row data, still *validates every loaded row* (`invalid: 0`) but emits a
  benign `WARN` that its own hardcoded expectation is 158; that warning reflects the route
  difference, not a defect. The Lean kernel decides the canonical 172-row set.
- `probes2/` is generated and git-ignored.
