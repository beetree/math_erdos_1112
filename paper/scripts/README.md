# Verification scripts

Run from the repository root:

```bash
python3 paper/scripts/check_short_proof.py --max 150
python3 paper/scripts/check_correspondence.py
cd lean
lake env lean Erdos1112Proof/AxiomsCheck.lean > /tmp/erdos1112-axioms.txt
python3 ../paper/scripts/check_axioms.py /tmp/erdos1112-axioms.txt
```

`check_short_proof.py` checks the paper’s explicit finite constructions and
inductive reduction using exact arithmetic. It uses no certificate tables.
The finite checks corroborate the proof; the general SHARP theorem is proved
in `lean/Erdos1112Proof/Short/Sharp.lean`.

`check_correspondence.py` checks every explicitly listed paper declaration
against its named source file. `check_axioms.py` requires every declaration
listed in the Lean audit and rejects axioms beyond Lean’s standard foundations.
Verification milestones are recorded in `PROGRESS.md`.
