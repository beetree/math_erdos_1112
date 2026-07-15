# Erdős #1112 — formal verification (Lean 4)

A complete, machine-checked proof of the dichotomy for
[Erdős Problem #1112](https://www.erdosproblems.com/1112). The prose proof it follows is in
[`../proof/`](../proof); start at the [proof index](../README.md).

## What is proved

Three theorems, all **`sorry`-free**, depending on **only the three standard Mathlib axioms**
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `native_decide`, no
`Lean.ofReduceBool`:

- `Erdos1112.erdos_1112` — `Question k d₁ d₂ ↔ k + 1 ≤ d₂` (the dichotomy), for `3 ≤ k`, `1 ≤ d₁ < d₂`.
- `Erdos1112.erdos_1112_existence_bound` — `RatioWorks k d₁ d₂ (192 · d₂)` when `k + 1 ≤ d₂`.
- `Erdos1112.erdos_1112_strong_nonexistence` — for `d₂ ≤ k`, every ratio sequence is defeated by a single `B`.

The theorems are stated against a **frozen statement file** [`Erdos1112.lean`](Erdos1112.lean) (which
carries the definitions and is never edited by the proof) and proved in the
[`Erdos1112Proof/`](Erdos1112Proof) development (50 files):
[`Erdos1112Proof/Final.lean`](Erdos1112Proof/Final.lean) states each theorem directly in terms of the
single frozen definitions — so the audited statement is literally what is proved, with no separate
copy to drift — and delegates the proofs to `namespace Erdos1112.Proof`. See §6 of the
paper ([`../paper/erdos1112.pdf`](../paper/erdos1112.pdf)) for why the frozen statement encodes the
informal problem, the trust base, and the full paper→Lean correspondence map (Appendix C).

## The proof development

[`Erdos1112Proof/`](Erdos1112Proof) is the proof, one file per lemma-cluster, each header carrying a
`Paper: §…` back-reference. This is what `lake build` builds and what the axiom/`sorry` gate checks.

## Setup — from zero to a verified build

`elan` reads [`lean-toolchain`](lean-toolchain) and installs the exact compiler
(`leanprover/lean4:v4.27.0`) automatically. `lake exe cache get` downloads the pinned Mathlib as a
prebuilt cache, so you don't recompile Mathlib from source (~30 min → a few minutes of download).

```bash
# 1. Install elan, the Lean version manager (picks up the pinned toolchain from lean-toolchain).
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 2. Get the repo and fetch the exact pinned Mathlib as a prebuilt cache.
git clone https://github.com/beetree/math_erdos_1112
cd math_erdos_1112/lean
lake exe cache get

# 3. Build the whole proof (a few minutes once Mathlib is cached).
lake build Erdos1112Proof
```

The dependency stack is frozen in [`lake-manifest.json`](lake-manifest.json)
(formal-conjectures rev `75573bb6`, Mathlib rev `a3a10db0e9`, Lean `v4.27.0`). **Do not run
`lake update`** — it would float the pins.

## Verify it yourself

`lake build` is the whole check. It compiles every file (so any `sorry` is a hard error) and, via
[`Erdos1112Proof/AxiomsCheck.lean`](Erdos1112Proof/AxiomsCheck.lean), prints the axiom audit as its
last step:

```
info: Erdos1112Proof/AxiomsCheck.lean:9:0: 'Erdos1112.erdos_1112' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Erdos1112Proof/AxiomsCheck.lean:10:0: 'Erdos1112.erdos_1112_existence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Erdos1112Proof/AxiomsCheck.lean:11:0: 'Erdos1112.erdos_1112_strong_nonexistence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Each line must show exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool`. To re-check without a full rebuild:

```bash
grep -rn 'sorry$' Erdos1112Proof --include='*.lean' | grep -v -- '--'   # zero sorries: expect no output
lake env lean Erdos1112Proof/AxiomsCheck.lean                           # re-print the three axiom lines
```

Two declarations are heavyweight and set a raised heartbeat budget locally
(`tailCovering_of_sturmian`, `exists_safe_subinterval`) — kernel-only, no `native_decide`.

## Paper → Lean map

Each part of the [prose proof](../README.md) maps to a directory here:

| Paper | Lean |
|---|---|
| §2 — Existence | [`Erdos1112Proof/Existence/`](Erdos1112Proof/Existence) — `existence_bound`, `exists_safe_subinterval` |
| §3 — Non-existence | [`Erdos1112Proof/NonEx/`](Erdos1112Proof/NonEx) — certificate, slot lemma, two-letter core, Sturmian/Morse–Hedlund |
| §4 — bounded subset-sum theorem | [`Erdos1112Proof/Sharp/`](Erdos1112Proof/Sharp) — the D/P/L/E/T/B case files, `hardcore_cases`, `sharp` |
| §5 — Assembly | [`Erdos1112Proof/Final.lean`](Erdos1112Proof/Final.lean) — the three theorems |

The full lemma-by-lemma correspondence table is Appendix C of the
paper ([`../paper/erdos1112.pdf`](../paper/erdos1112.pdf)).
