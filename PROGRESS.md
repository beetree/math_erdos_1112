# Short-proof migration progress

**Last updated:** September 12, 2026, 19:40 PDT

**Branch:** `simplify-paper`

**Checkpoint:** `de8aa9c` — short paper and checked initial Lean migration.

**Overall status:** Paper replacement implemented; full Lean migration in progress. No PR opened yet.

## Objective and completion rule

Replace the long paper with the supplied short proof and make the Lean development
follow that proof throughout, including the improved `d₂ + 2` theorem, the Kneser
density shortcut, the revised binary-word argument, and the table-free SHARP proof.
Retire obsolete proofs and certificates after their replacements pass.

A component is **verified** below only after its replacement compiles in Lean, or its
specified document/checking validation passes. An agent writing code does not count
as a completed formal proof. The full task is complete only when the final theorems
use the new arguments, the complete build and axiom audit pass, and the TeX/PDF and
correspondence documentation match that implementation.

## Milestones

| Milestone | Status | Evidence / remaining work |
|---|---|---|
| Create isolated branch | Done | `simplify-paper` |
| Replace paper source and PDF | **Verified document build** | Seven-page PDF; no layout warnings; independent review found no mathematical errors |
| Improved existence proof | **Verified** | `reciprocal_interpolation`, `existence_bound_reciprocal`, and headline `RatioWorks … (d₂ + 2)` compile; obsolete existence files removed |
| Elementary interval constructions | **Verified** | Coprime rectangle, interlacing, centered frame, and exact two-generator target bound |
| Slot lemma and final-summand sweep | **Verified** | `slots_from_run`, independent of old SHARP proof |
| Gcd normalization | **Verified** | `normalized_walk`: complete tail normalization, recurring alphabet, cardinality and gcd |
| New SHARP induction reduction | **Verified** | `sharpAt_of_funnel` compiles; dense-triple construction is its explicit remaining input |
| New SHARP paired movers | **Verified** | `paired_movers` and its exact `M−1` witness count compile and audit |
| Signed residue frames and even-case budgets | **Verified components** | Generic forward/reverse frames, `K` bound, even numerical cases and classification compile |
| Complete symmetric residue proof | In progress | Separate odd/even assembly agents |
| Revised critical two-letter argument | **Verified and integrated** | `binary_dichotomy` discharges the growth/covering input in `normalized_cases` |
| Finite Kneser dependency | **Verified** | `Finset.add_kneser` and strict refinement compile and audit cleanly |
| Odd-spacing SHARP exceptions | **Verified** | `spacing_one` and `spacing_two` compile |
| Kneser density shortcut | In progress; main dependency | Elementary pieces and finite Kneser verified; asymptotic-density theorem still open |
| Assemble new non-existence theorem | Pending | Requires SHARP, binary argument, and density shortcut |
| Remove obsolete non-existence / certificate machinery | Pending | Follows verified replacement assembly |
| Final full build, audit, paper correspondence, and PR | Pending | Component checks currently pass; migration is not complete |

## Active Sonnet agents

Five agents are running; the independent paper review has finished. All use `claude-leet --model claude-sonnet-5 --effort high`.
Each has separate file ownership. Codex handles shared lemmas, integration, validation,
and this report.

| Agent | Assignment | Current state | Owned output |
|---|---|---|---|
| `density` | Growth-to-density and periodicity-to-tail infrastructure | **Elementary pieces verified; agent finished.** Full Kneser remains open | `Short/Density.lean` |
| `kneser-finite` | Port an existing finite Kneser proof to pinned Lean/Mathlib | **Verified:** finite Kneser and strict refinement; agent finished | `Short/KneserFinite/` |
| `kneser-density` | Establish the passage to the density theorem | Resumed on source-backed e-transform dependencies and the weaker arithmetic-progression-tail consequence | `Short/KneserDensity*` |
| `sharp` / `eta-odd` | Paired movers, then complete odd residue cases | **Movers verified**; odd assembly active | `Short/Movers.lean`, `Short/EtaOdd.lean` |
| `funnel` / `residue-frame` / `eta-even` | Funnel and residue frames, then complete even residue cases | **Funnel and frames verified**; even assembly active | `Short/Funnel.lean`, `Short/ResidueFrame.lean`, `Short/EtaEven.lean` |
| `binary` / `binary-growth` / `density-iteration` | Binary proof, then density-count and sumset iteration bridges | **Complete binary dichotomy verified**; density bridge task active | `Short/Binary*`, `Short/DensityIteration.lean` |
| `odd-budget` | Odd residue-case budget inequalities | Formalizing arithmetic independently | `Short/OddBudget.lean` |
| `even-budget` | Even residue-case budget inequalities | **Verified, including maximal-K classification; agent finished** | `Short/EvenBudget.lean` |
| `spacing` | Two explicit odd-spacing SHARP exceptions | **Verified:** both constructions; agent finished | `Short/OddSpacing.lean` |
| `paper-review` | Independent mathematical review of shortened paper | **Finished:** no mathematical errors found; reported an earlier tooling issue already fixed | Review report; no repository edits |

Agent logs and interim reports are in `/tmp/erdos1112-agents/`. Those are live working
records, not durable proof artifacts; accepted results and findings will be summarized here.

## Verified results and checks

- [Reciprocal existence](lean/Erdos1112Proof/Existence/Reciprocal.lean): target build passes.
- [Intervals](lean/Erdos1112Proof/Short/Intervals.lean): target build passes.
- [Slots](lean/Erdos1112Proof/Short/Slots.lean): target build passes.
- [Normalization](lean/Erdos1112Proof/Short/Normalization.lean): target build passes.
- [Final theorem interface](lean/Erdos1112Proof/Final.lean): compiles with the improved existence bound.
- Axiom audit: 30 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Finite corroboration: all **77,770 dense triples through maximum 150** and **73,295 alphabets**
  checked by the new construction script pass. These finite checks are regression evidence,
  not a substitute for the general theorem.
- Paper correspondence: eleven explicitly listed declaration/file pairs pass the name check.
- PDF: seven pages, no LaTeX layout warnings on the last build; first and final pages inspected.

**Important boundary:** The current final non-existence theorem still imports the old
verified argument. Its successful build and audit do **not** certify full alignment
with the new paper. No replacement is being accepted with `sorry`, a custom axiom,
or an unproved Kneser assumption.

## Main open dependency

The pinned Mathlib lacks Kneser's density theorem. A finite Kneser proof was found in
another local Lean development and has now been ported and verified. The additional
asymptotic-density argument remains unformalized. Primary-source proofs have been
located for the next implementation phase. This remains the largest open part of
the migration.

## Next integration steps

1. Review and compile agent submissions; record exact completed lemmas here.
2. Assemble the SHARP theorem from the new induction and residue constructions.
3. Complete the density dependency and binary branch; assemble tail covering and the
   universal lacunary construction.
4. Replace the final non-existence imports and retire obsolete files.
5. Run the full build and audit, rebuild the PDF, finalize correspondence, and prepare the PR.

## Reproduction commands

From the repository root:

```bash
make -C paper
python3 paper/scripts/check_short_proof.py --max 150
python3 paper/scripts/check_correspondence.py
cd lean
lake build Erdos1112Proof.Existence.Reciprocal \
  Erdos1112Proof.Short.Intervals Erdos1112Proof.Short.Slots \
  Erdos1112Proof.Short.Normalization
lake env lean Erdos1112Proof/AxiomsCheck.lean > /tmp/erdos1112-axioms.txt
python3 ../paper/scripts/check_axioms.py /tmp/erdos1112-axioms.txt
```

## Progress log

- **19:06 PDT:** Created this report. Seven Sonnet agents active. Paper replacement,
  improved existence, interval helpers, slots, and normalization implemented and checked.
  Full non-existence / SHARP migration remains underway.

- **19:08 PDT:** Independent paper review finished with no mathematical errors found.
  Its correspondence-script finding referred to the earlier source and is already
  resolved; the current seven-entry correspondence check passes. Six formalization
  agents remain active.

- **19:10 PDT:** The complete normalized-walk interface now compiles. The audit has
  13 checked declarations and the paper correspondence lists eight replacements.
  The finite Kneser agent confirmed the required dependency APIs exist in our pinned
  Mathlib and has started adapting the proof source.

- **19:14 PDT:** The zero-liminf binary argument independently compiles, including
  the recurring-zero/balance contradiction, eventual width, and sweep. The agent
  has resumed on the growth alternative and normalization bridge. A separate agent
  is handling the two odd-spacing exceptions. Seven agents are active. The existence
  proof now uses the paper's exact closed reciprocal interval, including its endpoint.

- **19:17 PDT:** Elementary density interfaces independently compile: the growth
  count bound and the periodicity-to-tail implication. The density agent has finished;
  the full Kneser theorem remains assigned to the finite-port and density-extension
  agents. Six agents are active. The imported proof library currently builds successfully.

- **19:21 PDT:** The new inductive funnel independently builds. The agent is now
  working on the generic signed residue frames in parallel with the other SHARP work.
  A proposed density reduction was rejected: gcd one does not imply a cofinite
  sumset (residues 0 and 1 modulo 5 with k=3 give a counterexample). No theorem
  depends on that claim; the density agent is correcting its report and investigating
  the actual published density theorem.

- **19:23 PDT:** Split the odd and even residue-budget estimates into two further
  bounded Sonnet tasks. Eight agents are active; all use Sonnet 5 with high reasoning.

- **19:24 PDT:** Committed checkpoint `de8aa9c`. The seven-page paper, improved
  existence proof, interval lemmas, slots, normalization, zero-liminf binary branch,
  density interfaces, and inductive funnel are recorded together. Root library build
  and all 18 axiom checks pass. Full paper-aligned non-existence remains unfinished.

- **19:26 PDT:** Finite Kneser and its strict refinement independently pass, as do
  both explicit odd-spacing constructions. Their agents have finished. Six agents
  remain active. The finite theorem is now available to the density investigation.

- **19:31 PDT**: Full root library builds successfully (7,946 build jobs); all 22
  expected axiom checks pass. Five Sonnet agents are active. The density research
  task has finished; its theorem remains open, with primary-source proofs located.

- **19:38 PDT**: Paired movers and the complete binary dichotomy pass independent
  builds and axiom audits. The binary input is now discharged in the main case split.
  Root build passes with 24 audited declarations. Signed residue frames and even
  budgets also compile; two agents are assembling the full odd/even residue proofs.

- **19:40 PDT**: Root build passes with 30 audited declarations. The growth
  hypothesis now gives an explicit count bound. A separate agent is connecting
  growth to lower density and iterating the pending pairwise Kneser consequence;
  this does not assume that consequence has been proved.
