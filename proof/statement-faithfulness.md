*Erdős #1112 · [Index](../README.md) · Statement faithfulness*

# Statement faithfulness — the formal statement of Erdős #1112 and why it encodes the problem

This section concerns the **statement only** — the three `theorem` signatures and the definitions
they rest on — not the proof. It substantiates a single claim:

> **Faithfulness claim.** The Lean predicate `Erdos1112.Question k d₁ d₂` holds exactly when the
> informal "does $r_k(d_1,d_2)$ exist?" holds, and the three theorems `erdos_1112`,
> `erdos_1112_existence_bound`, `erdos_1112_strong_nonexistence` assert exactly the corresponding
> informal statements, under the stated hypotheses $k \ge 3$, $1 \le d_1 < d_2$.

Everything referenced below lives in two files in the repository, which is the primary artifact
(this document only reproduces them for reading):

- [`lean/Erdos1112.lean`](../lean/Erdos1112.lean) — the **frozen statement file**: the definitions
  and audit-helper lemmas. It is `import`-ed by the proof but never edited by it.
- [`lean/Erdos1112Proof/Final.lean`](../lean/Erdos1112Proof/Final.lean) — where the three theorems
  are *stated* (in `namespace Erdos1112`) directly in terms of the frozen definitions above, and
  *proved* by delegating to the development in `namespace Erdos1112.Proof`. There is a single copy of
  each definition, so the statement audited here is literally the one the theorems assert.

This document argues faithfulness of the *statement*. It does **not** — and cannot — establish that
the three theorems are actually proved; a faithful signature sitting on an unproved lemma would be
worthless. That the proofs are complete (`sorry`-free, resting only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`) is a separate, mechanical fact established by building
the repository — see [`lean/README.md`](../lean/README.md) and [Appendix D §D.2](appendix-D-lean.md).
Everything below is conditional on that build check.

---

## 1. The informal problem

Verbatim from [erdosproblems.com/1112](https://www.erdosproblems.com/1112):

> Let $1 \le d_1 < d_2$ and $k \ge 3$. Does there exist an integer $r$ such that if
> $B = \{b_1 < b_2 < \cdots\}$ is a lacunary sequence of positive integers with $b_{i+1} \ge r b_i$
> then there exists a sequence of positive integers $A = \{a_1 < a_2 < \cdots\}$ such that
> $d_1 \le a_{i+1} - a_i \le d_2$ for all $i \ge 1$ and $(kA) \cap B = \emptyset$, where $kA$ is the
> $k$-fold sumset?

Here $A$ and $B$ are infinite sets of positive integers, written as their strictly increasing
enumerations; $kA = \{x_1 + \cdots + x_k : x_1, \dots, x_k \in A\}$ is the $k$-fold sumset with
repetitions allowed. We use **"$r_k(d_1,d_2)$ exists"** as shorthand for the existence of such a
ratio $r$ — the problem asks only whether one exists (if a least threshold is wanted, take the least
natural witness after the integer-to-natural reduction of §3.8). It means precisely:

> there is an integer $r$ such that **every** lacunary $B$ of ratio $r$ admits **some** admissible
> $A$ (gaps in $[d_1,d_2]$) with $(kA) \cap B = \emptyset$.

The problem page lists the general existence question for $k \ge 3$ as open; the claimed resolution
formalized here is the dichotomy $r_k(d_1,d_2)$ exists $\iff d_2 \ge k+1$.

## 2. The formal statement (Lean 4)

The statement is the following two files, reproduced verbatim (file-header comments and `import`
lines elided). Sequences $A, B$ are functions `ℕ → ℕ`, 0-indexed (`b 0` is $b_1$, `b 1` is $b_2$, …).

[`lean/Erdos1112.lean`](../lean/Erdos1112.lean) — the frozen definitions and audit-helper lemmas:

```lean
namespace Erdos1112

/-- `B` (as a strictly increasing enumeration of an infinite set of positive
integers) is *lacunary with ratio `r`*: `b₁ ≥ 1`, `b₁ < b₂ < ⋯`, and
`b_{i+1} ≥ r · b_i` for all `i`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- `A` (as a strictly increasing enumeration of an infinite set of positive
integers) has all consecutive gaps in `[d₁, d₂]`:
`d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` (phrased additively; for `1 ≤ d₁`
this forces `A` strictly increasing). -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- For `1 ≤ d₁`, the gap condition forces `A` strictly increasing (audit
helper: makes explicit that `A` enumerates an infinite set). -/
lemma HasGapsIn.strictMono {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) : StrictMono a :=
  strictMono_nat_of_lt_succ fun i =>
    lt_of_lt_of_le (Nat.lt_add_of_pos_right hd₁) (h.2 i).1

/-- The `k`-fold sumset `kA` of the set enumerated by `a`:
all sums `a_{i₁} + ⋯ + a_{i_k}` (indices arbitrary, repetitions allowed). -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- The property asked for by the problem, for given `k`, `d₁`, `d₂` and a
candidate `r`: *every* lacunary sequence `B` with ratio `r` admits a set `A`
with gaps in `[d₁, d₂]` such that `(kA) ∩ B = ∅`. -/
def RatioWorks (k d₁ d₂ r : ℕ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWith r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

/-- `RatioWorks` is monotone in the ratio: a larger `r` only shrinks the class
of admissible `B`. This machine-checks the reduction from "an integer `r`" to
`r : ℕ` in `Question`: any integer witness may be replaced by any larger
natural one. -/
lemma RatioWorks.mono {k d₁ d₂ r r' : ℕ} (hrr' : r ≤ r')
    (h : RatioWorks k d₁ d₂ r) : RatioWorks k d₁ d₂ r' := by
  intro b hb
  exact h b ⟨hb.1, hb.2.1, fun i => (Nat.mul_le_mul hrr' le_rfl).trans (hb.2.2 i)⟩

/-- **Erdős Problem 1112** (erdosproblems.com/1112), verbatim question:

"Let `1 ≤ d₁ < d₂` and `k ≥ 3`. Does there exist an integer `r` such that if
`B = {b₁ < b₂ < ⋯}` is a lacunary sequence with `b_{i+1} ≥ r·b_i` then there
exists `A = {a₁ < a₂ < ⋯}` with `d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` and
`(kA) ∩ B = ∅`?"

I.e., for which `(k, d₁, d₂)` does `∃ r, RatioWorks k d₁ d₂ r` hold?
(Quantifying `r` over `ℕ` is equivalent to quantifying over `ℤ`; see the
header note.) -/
def Question (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, RatioWorks k d₁ d₂ r

/-- `B` is lacunary with a *varying* ratio sequence `R`:
`b_{i+1} ≥ R i · b_i` for all `i`. -/
def IsVarLacunaryWith (R : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, R i * b i ≤ b (i + 1)

/-- Constant-ratio varying lacunarity is exactly fixed-ratio lacunarity
(audit helper: the bridge used when instantiating the strong non-existence
theorem to refute `RatioWorks` at a constant ratio). -/
lemma isVarLacunaryWith_const_iff {r : ℕ} {b : ℕ → ℕ} :
    IsVarLacunaryWith (fun _ => r) b ↔ IsLacunaryWith r b :=
  Iff.rfl

end Erdos1112
```

[`lean/Erdos1112Proof/Final.lean`](../lean/Erdos1112Proof/Final.lean) — the three theorems, proved
from the development in `namespace Erdos1112.Proof`:

```lean
namespace Erdos1112

/-- Existence half with the paper's explicit ratio bound (target 2): when
`d₂ ≥ k + 1`, the concrete ratio `192 · d₂` works. -/
theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    RatioWorks k d₁ d₂ (192 * d₂) :=
  Proof.existence_bound k d₁ d₂ hk hd₁ hd h

/-- Non-existence half in the strong form (target 3, rev-4 constructive
`Nonempty`-intersection form). The underlying `Proof.strong_nonexistence` produces
the `¬ Disjoint` witness; `Set.not_disjoint_iff_nonempty_inter` exhibits the actual
collision point `kA ∩ B`. -/
theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        (kFoldSumset k a ∩ Set.range b).Nonempty := by
  obtain ⟨b, hb, hdef⟩ := Proof.strong_nonexistence k d₁ d₂ hk hd₁ hd h R
  exact ⟨b, hb, fun a ha => Set.not_disjoint_iff_nonempty_inter.mp (hdef a ha)⟩

/-- **Erdős Problem 1112, the dichotomy** (target 1): `r` exists iff
`d₂ ≥ k + 1`. Derived from the two halves exactly as in paper Part IV. -/
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    Question k d₁ d₂ ↔ k + 1 ≤ d₂ := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb, hdef⟩ :=
      erdos_1112_strong_nonexistence k d₁ d₂ hk hd₁ hd (by omega) (fun _ => r)
    obtain ⟨a, ha, hdisj⟩ := hr b (isVarLacunaryWith_const_iff.mp hb)
    exact (Set.not_disjoint_iff_nonempty_inter.mpr (hdef a ha)) hdisj
  · intro h
    exact ⟨192 * d₂, erdos_1112_existence_bound k d₁ d₂ hk hd₁ hd h⟩

end Erdos1112
```

## 3. Faithfulness, decision by decision

Each modeling decision is stated with the informal notion it renders, the reason it is faithful, and
the concrete way an encoding of this kind can go wrong (which we then check does not happen here).

### 3.1 Infinite increasing sets ↦ strictly increasing `ℕ → ℕ`
$A$ and $B$ are *infinite sets of positive integers*. Each is encoded by the function that
enumerates it in increasing order. The bijection between an infinite subset of $\mathbb{N}_{>0}$ and
its strictly increasing enumeration is standard, so no generality is lost. Strict monotonicity is
what makes the function an enumeration of a *set* (no repeated elements) rather than an arbitrary
sequence. *Failure mode avoided:* allowing non-monotone or finitely-supported sequences would model
multisets or finite sets. Here `StrictMono` is imposed on `B` directly (in `IsLacunaryWith`) and
*derived* for `A` (`HasGapsIn.strictMono`, using `1 ≤ d₁`), so both encode genuine infinite sets.

### 3.2 Positivity and indexing
`0 < b 0` and `0 < a 0` encode "positive integers": since the sequences are strictly increasing,
positivity of the first term gives positivity throughout. Indexing is 0-based, so `a 0` is the
site's $a_1$; this shifts names but not content, and the "for all $i$" conditions quantify over all
$i \in \mathbb{N}$, i.e. all consecutive pairs.

### 3.3 Lacunarity — `IsLacunaryWith r b`
`b_{i+1} ≥ r·b_i` for all $i$ is the site's ratio condition verbatim (`∀ i, r * b i ≤ b (i+1)`),
conjoined with positivity and strict monotonicity so that the admissible class of `B` matches
$\{b_1 < b_2 < \cdots\}$ of positive integers *for every candidate `r`* — including small `r` where
the ratio inequality alone would not force monotonicity. *This is a modeling decision:* "lacunary
with ratio `r`" is read as *exactly* the stated pointwise bound (plus positivity/monotonicity), with
no additional standard-lacunarity hypothesis read in. That is the natural reading of the quoted
problem, and it is conservative in both directions — a stronger reading of "lacunary" would shrink
the `∀ B` class (easier existence) and enlarge the non-existence construction's burden.

### 3.4 The gap window — `HasGapsIn d₁ d₂ a`
The site asks $d_1 \le a_{i+1} - a_i \le d_2$. Over `ℕ`, subtraction is truncated — it underflows to
`0` when $a_{i+1} < a_i$ — so the definition is phrased additively as
`a i + d₁ ≤ a (i+1) ∧ a (i+1) ≤ a i + d₂`. Under `1 ≤ d₁` the first inequality already forces
$a_i < a_{i+1}$, so `A` is strictly increasing; `HasGapsIn.strictMono` records exactly this
strict-increase consequence (not the full equivalence with the subtractive form). Once monotonicity
holds, the additive pair is equivalent to $d_1 \le a_{i+1} - a_i \le d_2$.

*Failure mode avoided:* with a subtractive phrasing the trap is the **upper** bound. On a decreasing
step `a (i+1) - a i` underflows to `0`, so an isolated `a (i+1) - a i ≤ d₂` reads `0 ≤ d₂` — **true** —
silently admitting negative gaps. (The lower bound is *not* the trap: a too-small positive gap gives
`d₁ ≤ (small)` = false, and an underflowed gap gives `d₁ ≤ 0` = false since `1 ≤ d₁`.) The additive
form avoids this, and — the practical reason `Nat.sub` is shunned in Lean — spares the proof the
$a_i \le a_{i+1}$ side-conditions that truncated subtraction demands before ordinary algebraic
rewrite lemmas apply.

### 3.5 The `k`-fold sumset — `kFoldSumset k a`
$kA = \{x_1 + \cdots + x_k : x_i \in A\}$ **with repetitions allowed**. The definition
`{ n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }` takes an *arbitrary* index function `f : Fin k → ℕ` with
no injectivity requirement, so the same element of $A$ may be picked more than once, and ranges over
all $k$-tuples of elements. *Failure mode avoided:* requiring `f` injective (or `StrictMono`) would
model the *distinct*-summand sumset $A^{\wedge k}$, a strictly smaller set, changing the problem.
The hypothesis `3 ≤ k` also makes the index type `Fin k` non-empty, so each element of $kA$ is a
genuine $k$-fold sum with no degenerate empty-sum ($k = 0$) case to worry about.

### 3.6 Avoidance — `Disjoint (kFoldSumset k a) (Set.range b)`
$(kA) \cap B = \emptyset$ is rendered as `Disjoint` of the two sets of naturals, with $B$ presented
as `Set.range b` (the set of values of the enumeration `b`, i.e. the set $B$ itself). In Mathlib,
`Disjoint s t` for sets is equivalent to `s ∩ t = ∅`, so this is the empty-intersection condition
exactly. The strong-nonexistence theorem uses the equivalent positive form
`(kFoldSumset k a ∩ Set.range b).Nonempty` (a *witnessed* collision), which is the negation of
`Disjoint`; the two are related by `Set.not_disjoint_iff_nonempty_inter` in `Final.lean`.

### 3.7 Quantifier structure — `RatioWorks` and `Question`
`RatioWorks k d₁ d₂ r` unfolds to `∀ b, IsLacunaryWith r b → ∃ a, HasGapsIn … ∧ Disjoint …`, and
`Question k d₁ d₂ := ∃ r, RatioWorks …`. So `Question` is `∃ r ∀ B ∃ A`, with `A` chosen **after**
`B` — exactly "does there exist `r` such that *for every* lacunary `B` *there exists* an `A` …".
*Failure mode avoided:* the weaker `∃ A ∀ B` (one `A` defeating all `B`) is a different, easier
statement; the definition here is the intended $\forall B\,\exists A$ order.

### 3.8 The ratio `r` over `ℕ` vs `ℤ`
The site says "an integer `r`"; the formalization quantifies `r : ℕ`. This loses no existence
content, by a two-line argument. ($\Leftarrow$) A natural witness *is* an integer witness, since
$\mathbb{N} \subseteq \mathbb{Z}$. ($\Rightarrow$) Given an integer witness $r$: if $r \ge 0$ it is
already a natural; if $r < 0$ the ratio condition is vacuous — `B` is positive, so
$r\,b_i \le 0 < b_{i+1}$ for every positive strictly increasing `B` — hence the admissible class is
the same as at $r = 0$, and $0$ is a natural witness. Either way a natural witness exists.

The lemma `RatioWorks.mono` (if `r` works then every `r' ≥ r` works, because a larger ratio only
shrinks the admissible class of `B`) is the one piece of this reduction rendered as machine-checked
Lean. The file does *not* define an integer-ratio predicate, so the full `ℤ`→`ℕ` bridge is an
informal justification of the modeling choice, not a proved equivalence; a formal bridge would add a
`RatioWorksInt` and prove it equivalent to `Question`.

### 3.9 The three theorems and the genuine `↔`
`erdos_1112` is a real bi-implication `Question k d₁ d₂ ↔ k + 1 ≤ d₂` under `3 ≤ k`,
`1 ≤ d₁ < d₂` — matching the site's "Let `1 ≤ d₁ < d₂` and `k ≥ 3`." Both directions are non-vacuous
and separately witnessed: `erdos_1112_existence_bound` makes the `←` half concrete (the explicit
ratio `192·d₂` works when `d₂ ≥ k+1`), and `erdos_1112_strong_nonexistence` makes the `→` half fail
concretely when `d₂ ≤ k`. Both sides of the `↔` are inhabited within the allowed parameter family, so
the equivalence is not vacuous: when `d₁ ≤ k`, the boundary `d₂ = k+1` realizes the existence side and
any `d₁ < d₂ ≤ k` realizes the non-existence side. (For `d₁ > k`, the hypothesis `d₁ < d₂` already
forces `d₂ ≥ k+2`, so only the existence side occurs there — consistent with the dichotomy.)

### 3.10 Strong non-existence and the varying-ratio bridge
`erdos_1112_strong_nonexistence` says **more** than $\lnot\,\texttt{Question}$: for *every* ratio
sequence `R : ℕ → ℕ` (possibly growing arbitrarily fast) there is a *single* `B` that is lacunary
with those varying ratios (`IsVarLacunaryWith R b`) and collides with the sumset of *every*
admissible `A`. This is the precise sense in which no *prescribed pointwise lower-ratio growth
sequence* for `B` can suffice. It implies the
plain non-existence used in `erdos_1112`: specializing `R ≡ r` (constant) via
`isVarLacunaryWith_const_iff` yields a fixed-ratio-`r` lacunary `B` defeating every admissible `A`,
i.e. `¬ RatioWorks k d₁ d₂ r`, for every `r` — hence `¬ Question`. `IsVarLacunaryWith` and
`isVarLacunaryWith_const_iff` are the two definitions that make this bridge explicit and checked.

## 4. Non-vacuity and sanity checks

None of the predicates is silently trivial, so neither the theorems nor their hypotheses are vacuous:

- `IsLacunaryWith r` is satisfiable for every `r`, e.g. `b i = (r+2)^i` — the base `r+2 ≥ 2` is
  strictly increasing and positive for *all* `r ∈ ℕ` (including `r = 0`, where `(r+1)^i` would be the
  constant `1` and fail `StrictMono`), and `r·(r+2)^i ≤ (r+2)^{i+1}`. So the `∀ B` in `RatioWorks`
  ranges over a non-empty class.
- `HasGapsIn d₁ d₂` is satisfiable, e.g. `a i = 1 + d₁·i` (each gap is `d₁ ∈ [d₁, d₂]`), so the
  `∃ A` obligation is over a non-empty class.
- `kFoldSumset k a` is always non-empty (it contains `k · a 0`, taking `f ≡ 0`), and `Set.range b`
  is infinite, so the `Disjoint` requirement is a genuine constraint — both it and its negation are
  achievable, so the theorems are not true (or false) for a trivial reason.

Separate from statement faithfulness, a proof-hygiene check confirms the theorems are genuinely
proved rather than stubbed: `#print axioms` on all three reports only

```
'Erdos1112.erdos_1112' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1112.erdos_1112_existence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1112.erdos_1112_strong_nonexistence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— no `sorryAx` (no gaps) and no `Lean.ofReduceBool` (no `native_decide` smuggling a kernel-unchecked
computation into a step). This concerns the *proof*, not the statement; the audit runs on every
`lake build` and is documented in [Appendix D §D.2](appendix-D-lean.md) and
[`lean/README.md`](../lean/README.md).

## 5. Correspondence: informal → Lean → file

| Informal notion (erdosproblems.com/1112) | Lean rendering | Location |
|---|---|---|
| $B=\{b_1<\cdots\}$ positive, lacunary ratio $r$ | `IsLacunaryWith r b` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| $A=\{a_1<\cdots\}$ positive, gaps in $[d_1,d_2]$ | `HasGapsIn d₁ d₂ a` (+ `.strictMono`) | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| $kA$, repetitions allowed | `kFoldSumset k a` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| $(kA)\cap B=\emptyset$ | `Disjoint (kFoldSumset k a) (Set.range b)` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| "$r$ works" (∀ B ∃ A) | `RatioWorks k d₁ d₂ r` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| "$r_k(d_1,d_2)$ exists" (∃ r …) | `Question k d₁ d₂` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| "integer $r$" ↔ `r : ℕ` | `RatioWorks.mono` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| varying-ratio $B$ / constant bridge | `IsVarLacunaryWith`, `isVarLacunaryWith_const_iff` | [`Erdos1112.lean`](../lean/Erdos1112.lean) |
| the dichotomy (answer to the question) | `erdos_1112` | [`Final.lean`](../lean/Erdos1112Proof/Final.lean) |
| existence with explicit bound $192 d_2$ | `erdos_1112_existence_bound` | [`Final.lean`](../lean/Erdos1112Proof/Final.lean) |
| strong non-existence (no ratio-floor sequence suffices) | `erdos_1112_strong_nonexistence` | [`Final.lean`](../lean/Erdos1112Proof/Final.lean) |

---
◀ [Index](../README.md) · Related: [Appendix D — Formal verification (Lean)](appendix-D-lean.md) · **Frozen statement file:** [`lean/Erdos1112.lean`](../lean/Erdos1112.lean)
