# Short-proof migration progress

**Last updated:** September 12, 2026, 20:30 PDT

**Branch:** `simplify-paper`

**Checkpoint:** `d87433a` — even SHARP and density infrastructure; next verified batch awaiting commit.

**Draft PR:** [#1](https://github.com/beetree/math_erdos_1112/pull/1)

**Overall status:** Paper replacement implemented; full Lean migration in progress. Draft PR open; not ready for final review.

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
| New SHARP induction reduction | **Verified** | `sharpAt_of_funnel` compiles; dense-triple input is discharged in `sharp_all` |
| New SHARP paired movers | **Verified** | `paired_movers` and its exact `M−1` witness count compile and audit |
| Signed residue frames and odd/even-case budgets | **Verified components** | Generic forward/reverse frames, `K` bound, both sets of budget cases, and even classification compile |
| Complete symmetric residue proof and SHARP | **Verified and integrated** | `eta_even`, `eta_odd`, and closed `sharp_all` build and audit; all SHARP callers now use the new proof |
| Revised critical two-letter argument | **Verified and integrated** | `binary_dichotomy` discharges the growth/covering input in `normalized_cases` |
| Finite Kneser dependency | **Verified** | `Finset.add_kneser` and strict refinement compile and audit cleanly |
| Odd-spacing SHARP exceptions | **Verified** | `spacing_one` and `spacing_two` compile |
| Kneser density shortcut | In progress; main dependency | Growth-to-density, iteration, and e-transform density invariance verified; the weak pairwise law remains open |
| Density limit argument | **Verified component** | Least-choice fairness, finite absorption, survivor-to-progression and finite-prefix deletion; actual transformation sequence remains to be connected |
| Assemble new non-existence theorem | Pending | Requires complete SHARP and density shortcut; binary alternative is integrated |
| Remove obsolete non-existence / certificate machinery | **SHARP/certificates removed** | Old SHARP case tree and table generators/data/harnesses deleted; old non-existence case proofs await density completion |
| Final full build, audit, paper correspondence, and PR | Pending | Component checks currently pass; migration is not complete |

## Active Sonnet agents

**Concurrency target: ten Sonnet subagents.** At this update, **10 processes were running**.
All use `claude-leet --model claude-sonnet-5 --effort high`. Completed workers
are reassigned to independent remaining work; Codex handles integration,
verification, shared interfaces, cleanup, and this report.

Current process names: `binary-core-migration`, `kneser-weak-assembly`, `kneser-block-sequence`, `kneser-bounded-data`, `kneser-frame`, `nonex-infrastructure-migration`, `short-main-assembly`, `kneser-density-scaling`, `kneser-subsequence`, `short-sharp-audit`.

Agent logs and interim reports are in `/tmp/erdos1112-agents/`. Those are live
working records; durable accepted results are recorded in the milestones and commits.
Agents have separate file ownership. A submitted result counts as verified only
after independent checking, and an explicitly conditional lemma does not discharge
its remaining hypothesis.

## Verified results and checks

- [Reciprocal existence](lean/Erdos1112Proof/Existence/Reciprocal.lean): target build passes.
- [Intervals](lean/Erdos1112Proof/Short/Intervals.lean): target build passes.
- [Slots](lean/Erdos1112Proof/Short/Slots.lean): target build passes.
- [Normalization](lean/Erdos1112Proof/Short/Normalization.lean): target build passes.
- [Final theorem interface](lean/Erdos1112Proof/Final.lean): compiles with the improved existence bound.
- Axiom audit: 72 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Finite corroboration: all **77,770 dense triples through maximum 150** and **73,295 alphabets**
  checked by the new construction script pass. These finite checks are regression evidence,
  not a substitute for the general theorem.
- Paper correspondence: twelve explicitly listed declaration/file pairs pass the name check.
- PDF: seven pages, no LaTeX layout warnings on the last build; first and final pages inspected.

**Important boundary:** The current final non-existence theorem still imports the old
verified argument. Its successful build and audit do **not** certify full alignment
with the new paper. No replacement is being accepted with `sorry`, a custom axiom,
or an unproved Kneser assumption.

## Main open dependency

The pinned Mathlib lacks Kneser's density theorem. A finite Kneser proof was found in
another local Lean development and has now been ported and verified. The asymptotic-density proof now has verified finite Mann, transformation,
stabilization, block-estimate, compression-count, and translation components.
Its final compression and case assembly remain the largest open part of the migration.

| Density dependency | Status |
|---|---|
| Counts, lower-density definitions and e-transform identities | Verified, including joint-density invariance |
| Finite Mann count inequality | Verified: `mann_count`; independent target and root builds pass |
| Long-block density estimate | Verified with explicit Mann input; actual Mann is available and sequence assembly is active |
| Fairness, limit survivors, finite-prefix deletion and progression growth | Verified abstract components |
| Residue compression and density rescaling | Algebra and bounded count error verified; density rescaling active |
| Growth-to-density and iteration over `k` summands | Verified and integrated; Kneser remains an explicit input |
| Concrete transformation sequence | Verified: fairness, sumset containment, invariant joint density |
| Finite second sets, residue minima, modular interval generation | Verified components |
| Complete bounded/unbounded density argument | Remaining compression and case assembly |

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

- **19:50 PDT**: Draft PR #1 is open; its finite-construction CI passes and Lean CI
  is running. Local root build passes with 37 audited declarations. Both odd/even
  budget families are verified. The new fairness/limit lemmas also pass; the
  density transformation process and its full density bound are still unfinished.

- **19:57 PDT**: Both checks on PR #1 are green. The local root build passes
  with 41 audited declarations, including the new fair transformation-sequence
  construction and limit lemmas. The sequence construction has explicit operation
  laws; connecting the concrete maximal transform and proving the zero-limit
  density bound remain required.

- **20:11 PDT**: Increased to ten running Sonnet 5 agents at the user’s request.
  The complete even SHARP theorem, e-transform density invariance, and density
  iteration independently build. Only the odd residue assembly remains for SHARP.
  The density route is split into concrete independent tasks, plus a mathematical
  review; its weak pairwise law is still unproved.

- **20:22 PDT**: Ten live Sonnet workers confirmed after reassigning completed tasks. Finite Mann, modular subset-sum covering, finite grids and interval growth, compression counts, and translation density invariance independently build. Root build passes with 72 audited declarations. SHARP induction assembly compiles with the odd case as its explicit remaining input. Independent review identified the need to handle finite second sets before using the infinite-set block estimate; a worker is closing this directly via zero density.

- **20:30 PDT**: Closed `sharp_all` independently builds; new SHARP is integrated and the entire old SHARP proof/certificate layer is removed. The PDF remains seven pages with 12 correspondence entries. The 72-declaration root audit passes. Finite Mann, long-block estimate, concrete transforms, stabilization, minima, finite-right density and scaled grid constructions are verified components; final density assembly remains open.
