*Erdős #1112 · [Index](../README.md) · Appendix D*

## Appendix D. Formal verification (Lean 4)

The complete dichotomy has been formalized in Lean 4. The development (and the verification scripts
of Appendix C) are available at
[https://github.com/beetree/math_erdos_1112](https://github.com/beetree/math_erdos_1112). Its
faithfulness to the informal problem is treated in its own standalone section, [**Statement faithfulness**](statement-faithfulness.md) (§D.1
below is a pointer to it). This appendix records the trust base (§D.2), the structure and drift
guards (§D.3), a map from paper results to Lean declarations (§D.4), reproduction instructions and
checksums (§D.5), and the deviation ledger (§D.6).

### D.1 Statement faithfulness

A `sorry`-free proof of the *wrong* statement proves nothing, so the formal statement and every
definition it depends on are made explicit and justified against the informal problem. That argument
is now a self-contained section — [**Statement faithfulness**](statement-faithfulness.md) — so it
can be reviewed on its own: it reproduces the problem (with the erdosproblems.com/1112 reference),
the full Lean encoding from the frozen [`Erdos1112.lean`](../lean/Erdos1112.lean), a
decision-by-decision faithfulness argument (quantifier order, the repetition convention, the additive
gap phrasing, the `ℤ`-vs-`ℕ` reduction, the strong-nonexistence bridge), non-vacuity checks, and an
informal→Lean→file correspondence table.

In brief: the frozen file (namespace `Erdos1112`; `A`, `B` encoded as strictly increasing `ℕ → ℕ`,
0-indexed) defines `Question k d₁ d₂ := ∃ r, RatioWorks k d₁ d₂ r`, and the three theorems
`erdos_1112`, `erdos_1112_existence_bound`, `erdos_1112_strong_nonexistence` — proved in
[`Erdos1112Proof/Final.lean`](../lean/Erdos1112Proof/Final.lean) — assert the dichotomy, the explicit
existence bound `192·d₂`, and the strong non-existence form, all under `3 ≤ k`, `1 ≤ d₁ < d₂`.

### D.2 Trust base (axioms)

The proof development is `sorry`-free: a source scan finds no `sorry` tactic, no `axiom`
declaration, and no `native_decide`/`Lean.ofReduceBool` anywhere in `Erdos1112Proof/` (all of
`(SHARP)` — Theorem 3 — is proved, not assumed). Consequently the axiom audit, produced by the
`#print axioms` command of the recipe in §D.5, reports for each of the three theorems exactly

```
[propext, Classical.choice, Quot.sound]
```

— the three standard foundational axioms of Lean/Mathlib and nothing else. In particular no
`sorryAx` and no `Lean.ofReduceBool`: every finite/decidable check (the certificate tables of
Proposition FV, the `a ≤ 3000` T-scan, the small-`a` corners) is closed by the trusted **kernel**,
not by compiled `native_decide` code — so the trusted base is Lean + Mathlib only, not the Lean
compiler. This is the expected clean result; the recipe in §D.5 reproduces it. These axiom lines
should be regenerated from a clean checkout rather than taken on the strength of this transcript.

### D.3 Structure and fidelity

The frozen `Erdos1112.lean` contains only the definitions encoding the problem (`Question`,
`RatioWorks`, `HasGapsIn`, `kFoldSumset`, `IsLacunaryWith`, `IsVarLacunaryWith`) plus small helper
lemmas — no theorem stubs. The development `Erdos1112Proof/` (namespace `Erdos1112.Proof`) proves the
engine lemmas; the three targets are then stated once each, directly, in `Erdos1112Proof/Final.lean`
(namespace `Erdos1112`) over those frozen definitions, with proofs delegated to the `Erdos1112.Proof`
development. There is a single statement of each target — no duplicate copy — so nothing can drift;
statement fidelity rests on the frozen definitions (§D.1), which the theorems reference directly.

- The layout mirrors the paper: `Existence/` (Part I), `NonEx/` incl. `NonEx/TwoLetter/` and the
  Morse–Hedlund subtree `NonEx/TwoLetter/MH/` (Part II), and `Sharp/` (Part III — one file per
  case `CaseD`, `CaseP`, `CaseL`, `CaseE`, `CaseT…`, `CaseB`, plus `Frame`, `Lift`, `Staircase`,
  `Graham`, `Tables`).

### D.4 Correspondence map (paper → Lean)

Every numbered result maps to a formal declaration (namespace `Erdos1112.Proof`, files relative to
`Erdos1112Proof/`). Every listed paper lemma is load-bearing for the Lean main theorems: the
development formalizes the full case tree rather than citing anything externally.

| Paper result | Lean declaration | File |
|---|---|---|
| Theorem 1 (existence) | `existence_bound`; free-gap `exists_safe_subinterval` | `Existence/Nested.lean`, `Existence/FreeGap.lean` |
| Main Thm / Thm 1 / strong non-ex. (headline) | `erdos_1112`, `erdos_1112_existence_bound`, `erdos_1112_strong_nonexistence` | `Final.lean` |
| Lemma 2.1 (certificate) | `cert_hit`, `strong_nonexistence_of_tailCovering` | `NonEx/Certificate.lean` |
| Lemma 2.3 (AP tail) / 2.5 (periodic) | `tailCoveringN_of_single_letter` / `…_of_eventually_periodic` | `NonEx/GapWord.lean` |
| Lemma 2.6 (interval) / 2.7 (sweep) | `Wset_interval` / `sweep` | `NonEx/TwoLetter/Core.lean` |
| Lemma 2.8 (width dichotomy) | `width_of_unbalanced`, `balancedQ_of_no_widthTwo` | `NonEx/TwoLetter/Core.lean`, `…/Balanced.lean` |
| Lemma 2.9 (boundary, $k$ even) | `width_even_boundary` (+ `palindrome_of_qCount_const`, `period_of_two_palindromes`) | `NonEx/TwoLetter/Core.lean` |
| Lemma 2.10 (Sturmian) | `tailCovering_of_sturmian`; `uniform_syndeticity`, `walk_enters` | `…/Sturmian.lean`, `…/MH/Walk.lean` |
| — MH slope / oscillation / mechanical | `slope`, `disc_osc_le_one`, `mechanical_tail`, `balanced_classification` | `…/MH/Slope.lean`, `…/MH/IrrationalCase.lean`, `…/Balanced.lean` |
| Lemma 2.12 (Slot) | `tailCovering_of_three_letters`, `slot_core_gcd_one` | `NonEx/SlotLemma.lean` |
| Lemma 3.2 (frame) / 3.3 (staircase) / 3.4 (λ-lift) | `frame_lemma` / `staircase_phase_base`, `…_extended`, `staircase_merge_c` / `FrameCert.lift` | `Sharp/Frame.lean`, `Sharp/Staircase.lean`, `Sharp/Lift.lean` |
| Lemma 3.5 (Graham) / 3.10 (L4) | `sharpAt_of_hardcore` / `sharp_of_minimal` | `Sharp/Graham.lean` |
| Case D / P (pair-frame + ETAneg) / L / E | `caseD` / `caseP_pair`, `caseP_large` / `caseL` / `caseE` | `Sharp/CaseD.lean`, `Sharp/CaseP.lean`, `Sharp/CaseL.lean`, `Sharp/CaseE.lean` |
| Case T (+ `tSuppT`) / Case B (+ descent) | `caseT`, `T_tail_line`, `tSuppT` / `caseB`, `rowFor`, `caseBComplete` | `Sharp/CaseT*.lean` / `Sharp/CaseB.lean`, `Sharp/CaseBClasses.lean` |
| dispatch / Theorem 3 (SHARP) | `hardcore_cases` / `sharp` | `Sharp/Main.lean` |
| axiom audit | three `#print axioms` commands | `AxiomsCheck.lean` |

Infrastructure with no paper number but load-bearing: Lemma 2.2 tail index (`exists_tail_index`),
Lemma 2.4 rescaling (`tailCoveringN_of_rescaled`), the frame-certificate API
(`frameCertOK`, `certTableA/B` in `Sharp/Tables*.lean`). No listed paper result lacks a Lean
counterpart.

### D.5 Reproducibility, toolchain, and checksums

- **Toolchain (pinned):** `leanprover/lean4:v4.27.0` (`lean-toolchain`); Mathlib pinned via
  `lake-manifest.json` (dependency snapshot `formal_conjectures` rev `75573bb6`, Mathlib rev
  `a3a10db0e9`). The proof is 50 files.
- **Repository:** [https://github.com/beetree/math_erdos_1112](https://github.com/beetree/math_erdos_1112);
  the Lean development is in `lean/` (`Erdos1112.lean` + the 50-file `Erdos1112Proof/`), with build
  and verification instructions in [`lean/README.md`](../lean/README.md).
- **SHA256 checksums** (the repository files, not the typeset appendix, are the canonical
  executable artifacts):

  ```
  d9893b6a8968b903533467fa0c2b4cb9eeb32007182d4b22d847ab852b9658d0  sharp6_final.py
  8502fbe55b037716beedcaf21ad03008be5f25d1f38acd79a50c8de0ed8fd6a0  sharp_referee_check.py
  762d9e514dd0e6c8a38d12d58242922f3cd2ca1c3900c9d78189d6325e967f3b  probes2/sharp_tables.txt
  ```

- **Minimal verification route** (minutes, modulo a prebuilt Mathlib): build the three theorem
  statements and print their axioms; run both Python scripts at `Mmax = 120`; check zero script
  failures.

  ```bash
  lake build Erdos1112Proof                                     # 1. build the library
  grep -rIn 'sorry$' Erdos1112Proof --include='*.lean' | grep -v -- '--'   # 2. expect no output
  echo 'import Erdos1112Proof
  #print axioms Erdos1112.erdos_1112
  #print axioms Erdos1112.erdos_1112_existence_bound
  #print axioms Erdos1112.erdos_1112_strong_nonexistence' > /tmp/check.lean
  lake env lean /tmp/check.lean                                 # 3. expect the 3-axiom list, thrice
  python sharp6_final.py 120                                    # 4. DESIGNATED-BRANCH FAILURES: 0
  python sharp_referee_check.py 120                             # 5. FATAL/CONSTRUCTION FAILURES: 0
  ```

- **Full verification route:** build all 50 files; let the kernel discharge every table/scan check
  (Proposition FV); regenerate Tables A/B and both scripts' stdout and diff against Appendices A–B.
- Two declarations are heavyweight and set a raised kernel heartbeat locally
  (`tailCovering_of_sturmian`, `exists_safe_subinterval`) — kernel-only, no added trust cost.
- **Reproduction.** The `sorry`-free / three-axiom result is reproducible from a clean checkout via
  the recipe above (run against the pinned toolchain). The published version additionally carries an
  archived snapshot (DOI) and a continuous-integration build log exhibiting the green `lake build`
  and the `#print axioms` output, so a reader can confirm the result without re-running the build.

### D.6 Deviation ledger (all simplifying; none a correction)

Each item keeps the target theorem signatures (built from the frozen definitions) exactly and is
kernel-checked. This is the complete
list of departures from the manuscript, cross-referenced from the "Effect of the formalization"
note in the Attribution section. Every departure is a simplification we have incorporated into the
paper proof above; none is a correction.

1. **Case P — uniform pair-frame (§III.4).** One `r`-parameterized construction (Lemma 3.12)
   replaces the separate `r = 3`/`r = 4` families, the three ad-hoc `r = 5` certificates, and the
   `a < 15` finite check; the reach closes symbolically for `a ≥ 8` and the residual `a ≤ 7`
   triples are decided, so the formal proof runs **no** subset-sum search in Case P. The
   `a`-even `b = M-1` corner of Lemma 3.14 is proved vacuous by parity.
2. **Case D — uniform construction (§III.3).** The `q = 2`/`q ≥ 3` split and the `e = a-1`
   endpoint are removed; the budget closes uniformly on `(a-1)(q-2) ≥ 0`.
3. **Two-letter core — density-free route (§II.3).** The balanced-classification/threshold
   separation is obtained from a discrepancy-oscillation iteration (`disc_osc_le_one`), and
   uniform syndeticity (Sturmian Step 1) from an explicit Dirichlet-step circle walk — neither
   uses density, equidistribution, three-distance, or Morse–Hedlund as a black box; Dirichlet's
   approximation theorem is the only analytic input.
4. **Part I — single free gap (§1.2).** The safe subinterval is produced at the single index
   `s₁ = ⌈t/d₂⌉` with safety-for-all-`s` by monotonicity, in place of the relevance-interval /
   endpoint-spacing count.
5. **Case T — merge-lemma-free variant (§III.7).** Only the two merge-robust staircase variants
   (A and base form) are run; the `14` additional budget failures are discharged by decided
   frame-box rows (`tSuppT`), so Case T does not depend on Lemma 3.3(c).
6. **Case T variant-B → 14 supplementary rows; statement form.** The Table A/B certificate rows are
   kernel-checked as 360 rows (Table A 158 + Table B 172 main + 30-row re-basing supplement,
   deduplicating to the `158 + 178` distinct classes of Appendix B) by `certTableA_ok` / `certTableB_ok`;
   the 14 supplementary `tSuppT` rows are decided separately by `tSuppT_ok`, for 374 kernel-decided
   rows in all. `erdos_1112_strong_nonexistence` uses the constructive `Set.Nonempty` form.

Formalizing the tables and scans exposed no erroneous, missing, or redundant object; the extended
form of Lemma 3.3(d), whose pre-repair statement was false, is carried in its repaired form and its
counterexample `(5,7,9)` is pinned as a decided guard.


---
◀ [Appendix C — Verification scripts](appendix-C-scripts.md) · **Up:** [Proof index](../README.md) · **Build & verify:** [`lean/README.md`](../lean/README.md)
