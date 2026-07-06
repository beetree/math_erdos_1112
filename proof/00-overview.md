*Erdős #1112 — guided proof · [Proof index](../README.md)*

# The dichotomy for Erdős problem #1112: $r_k(d_1,d_2)$ exists if and only if $d_2 \ge k+1$

**Abstract.** For integers $k \ge 2$ and $1 \le d_1 < d_2$, let $r_k(d_1,d_2)$ denote the least
integer $r$ (if one exists) such that for every lacunary sequence $B = \{b_1 < b_2 < \cdots\}$ of
positive integers with $b_{i+1} \ge r\,b_i$ there is a sequence $A = \{a_1 < a_2 < \cdots\}$ with
$d_1 \le a_{i+1} - a_i \le d_2$ for all $i$ and $(kA) \cap B = \emptyset$, where $kA$ is the
$k$-fold sumset. We prove the complete dichotomy: **for every $k \ge 3$ and $1 \le d_1 < d_2$, the
number $r_k(d_1, d_2)$ exists if and only if $d_2 \ge k+1$.** Existence comes with the explicit
bound $r_k(d_1,d_2) \le 192\,d_2$; non-existence holds in the strong form that no growth condition
whatsoever on $B$ suffices. The proof of the non-existence side reduces, after a word-combinatorial
analysis (balanced words, Morse–Hedlund, Sturmian ladders) and an amortized "slot" argument, to a
finite additive-combinatorics lemma — (SHARP): every finite set $G$ of at least three positive
integers with $\gcd(G) = 1$ and $\max(G) = M$ admits a multiset of at most $M-1$ of its elements
whose subset sums contain $M$ consecutive integers — which we prove in full. The proof of (SHARP)
is computer-assisted in the precise, finite, re-runnable sense described in Appendix A. The entire
dichotomy — all three theorems, including the strong non-existence form — has moreover been
formally verified in Lean 4: the proof is machine-checked, `sorry`-free, and depends only on
Lean's three standard foundational axioms, checked against a verbatim transcription of the problem
statement (Appendix D). The Lean development and verification scripts are available at
[https://github.com/beetree/math_erdos_1112](https://github.com/beetree/math_erdos_1112).

---

## 1. The problem and prior results

From erdosproblems.com/1112 (verbatim):

> "Let $1\leq d_1<d_2$ and $k\geq 3$. Does there exist an integer $r$ such that if
> $B=\{b_1<\cdots\}$ is a lacunary sequence of positive integers with $b_{i+1}\geq rb_i$ then
> there exists a sequence of positive integers $A=\{a_1<\cdots\}$ such that
> $d_1\leq a_{i+1}-a_i\leq d_2$ for all $i\geq 1$ and $(kA)\cap B=\emptyset$, where $kA$ is the
> $k$-fold sumset?"

and, from the page's remarks: "The more general question of existence of $r_k(a,b)$ for $k\geq 3$
remains open."

Prior results:

- **[ErGr80], [BHJ97]:** $r_2(2,3) = 2$.
- **[Ch00]:** $r_2(a,b) \le 2$ for $a < b$ (with the $b = 2a$ reading fixed as in the problem
  page's comment thread).
- **[BHJ97]:** $r_3(2,3)$ does not exist, in a strong form.
- **[TaYa21]** (Tang–Yang, Publ. Math. Debrecen 99 (2021), 485–493) prove, for $k \ge 3$, that if
  the difference sequence of $A$ is of *block type* then there is a $B$ with $(kA) \cap B \ne
  \emptyset$ (their abstract, verbatim). That restricted class is already handled by our Lemma 2.5
  (eventually periodic tails); the strong non-existence theorem here resolves **every** $d_2 \le k$
  unconditionally, including the non-periodic (Sturmian) tails that carry the difficulty. The
  existence side (Theorem 1) and the dichotomy viewpoint appear to be new.

## 2. Main theorem

**Main Theorem.** Let $k \ge 3$ and $1 \le d_1 < d_2$.

1. *(Existence.)* If $d_2 \ge k + 1$ then $r_k(d_1, d_2)$ exists; explicitly
   $r_k(d_1,d_2) \le 192\,d_2$ (the constant is not optimized; the method gives $\approx 8 d_2$
   with sharper bookkeeping).
2. *(Non-existence, strong form.)* If $d_2 \le k$ then $r_k(d_1, d_2)$ does not exist — indeed,
   for **every** sequence $r_1 \le r_2 \le \cdots$ there is a single $B$ with
   $b_{i+1} \ge r_i b_i$ such that $(kA) \cap B \ne \emptyset$ for **every** $(d_1,d_2)$-sequence
   $A$.

Hence $r_k(d_1,d_2)$ exists $\iff d_2 \ge k+1$, and the answer to the quoted question is:
**yes precisely when $d_2 \ge k+1$.** Note that $d_1$ is irrelevant to the threshold.

*The $k = 2$ context (stated separately, not part of the Main Theorem):* $r_2(2,3) = 2$
[ErGr80, BHJ97]; $r_2(a, b) \le 2$ [Ch00]. The strong form of non-existence is **not** claimed at
$k = 2$: the width machinery of Part II genuinely fails there (a mirror-extension word with
palindromic prefixes at lengths $94, 190, 382, 766, \dots$ forces two-index antidiagonal width $0$
infinitely often), which is why Part II requires $k \ge 3$. The consecutive-window dichotomy
$r_k(d, d+1)$ exists $\iff d \ge k$ is exactly the $d_2 = d + 1$ slice of the Main Theorem, for
every $k \ge 3$.

## 3. Notation

For a $(d_1,d_2)$-sequence $A = \{a_1 < a_2 < \cdots\}$ write $g_n := a_{n+1} - a_n \in
[d_1, d_2] \cap \mathbb{Z}$, $p_0 := 0$, $p_n := g_1 + \cdots + g_n$, so $a_{n+1} = a_1 + p_n$ and
$$kA = k a_1 + \{ p_{i_1} + \cdots + p_{i_k} : i_1, \dots, i_k \ge 0 \}.$$
A sequence $A$ is **tail-covering** if $kA \supseteq \{x \ge X_0 : x \equiv \rho \pmod m\}$ for some
$m \ge 1$, $\rho$, $X_0$ ([`NonEx/TailCovering.lean`](../lean/Erdos1112Proof/NonEx/TailCovering.lean)). $G_\infty$ denotes the set of gap values of $A$ occurring infinitely
often ("the tail alphabet"). For a finite multiset $S$ of positive integers,
$\text{subset-sums}(S) := \{\sum_{x \in T} x : T \subseteq S\}$ (as a multiset selection). For a
finite set $G$ of positive integers with $M := \max G$,
$$m(G) := \min\{\, |S| : S \text{ a multiset drawn from } G,\ \text{subset-sums}(S) \supseteq
\text{an interval of } M \text{ consecutive integers} \,\}.$$
Intervals of integers are written $[u, v] = \{u, u+1, \dots, v\}$.

---

## 4. Proof architecture and trust model

This paper is a **computer-assisted proof in the following limited sense**: all infinite
mathematical reductions — Parts I and II, and every asymptotic ("all $M$") construction in Part
III — are proved in the text; the only finite checks are the explicitly listed table/certificate
checks of Appendix B, independently checked by the scripts of Appendix C and by the Lean kernel.
The Lean development is **not** used as an oracle for unstated mathematics: wherever the formal
proof differs materially from the paper proof, the corresponding human-readable lemma is stated
and proved in the text (the differences are simplifications, listed in §D.6).

**Three layers, three jobs.** We keep the following distinctions sharp, so no claim is misread as
resting on more than it does.

- The **prose** is the human-readable proof; a referee is asked to accept the theorem on the
  strength of the prose alone. Python is corroboration; Lean is certification.
- The **Python** (Appendix C) verifies the **finite layer only**: the subset-sum certificates and
  the exhaustion of the hard-core decision tree for $M \le 120$. Each covering multiset
  self-certifies $m(G) \le M-1$; this is independently reproducible and touches nothing asymptotic.
- The **asymptotic lemmas** (Part I, Part II, and the all-$M$ reach/tail/slope arguments of Part
  III) are proved in prose and formalized in Lean; the Python never touches them.
- Only the **Lean** development certifies the **entire** argument, finite and infinite together.

In particular the Python does not "verify the theorem" — it verifies a component. Every step falls
into exactly one of three auditable categories: **(1)** an ordinary handwritten proof in the text;
**(2)** a finite certificate check, with all data and code supplied and reproducible (Appendices
B–C, Proposition FV); **(3)** a Lean-verified statement, with an exact theorem name and source
file (Appendix D).

**What a reader must trust.** The non-formal part requires ordinary mathematical checking of the
lemmas of Parts I–III. The finite part requires either checking the listed certificates by hand,
running the supplied Python, or trusting the Lean kernel's re-check. The formalized theorem
requires trusting Lean, Mathlib, and the transcription of the problem in `Erdos1112.lean` — whose
faithfulness to the informal problem is argued in full in the
[Statement faithfulness](statement-faithfulness.md) section. This is the honest trust
base; "machine-checked" alone would hide the one real question, which is always the bridge between
the formal statement and the informal theorem.

**Dependency table.** Each principal result, classified by where its proof lives. "Prose" = fully
proved here; "Python" = corroborated by the Appendix C scripts; "Lean" = the formal declaration
(namespace `Erdos1112.Proof`) and file; "Data" = finite certificate input required. The full Lean
map is §D.4.

| Paper result | Role | Prose | Python | Lean declaration (file) | Data |
|---|---|:--:|:--:|---|:--:|
| Theorem 1 | existence bound $r_k \le 192 d_2$ | ✓ | spot | `existence_bound` (`Existence/Nested.lean`) | — |
| Lemma 2.1 | certificate / diagonalization | ✓ | — | `cert_hit` (`NonEx/Certificate.lean`) | — |
| Lemma 2.7 | width $\Rightarrow$ tail-covering | ✓ | — | `sweep` (`NonEx/TwoLetter/Core.lean`) | — |
| Lemma 2.9 | two-letter boundary ($k$ even) | ✓ | — | `width_even_boundary` (`NonEx/TwoLetter/Core.lean`) | — |
| Lemma 2.10 | Sturmian case | ✓ | — | `tailCovering_of_sturmian` (`NonEx/TwoLetter/Sturmian.lean`) | — |
| Lemma 2.12 | Slot lemma ($\ge 3$ letters) | ✓ | — | `tailCovering_of_three_letters` (`NonEx/SlotLemma.lean`) | — |
| Lemma 3.2 | frame: box $\Rightarrow$ interval | ✓ | ✓ | `frame_lemma` (`Sharp/Frame.lean`) | — |
| Lemma 3.4 | $\lambda$-lift | ✓ | ✓ | `FrameCert.lift` (`Sharp/Lift.lean`) | — |
| Lemma 3.5 | Graham reduction to hard core | ✓ | ✓ | `sharpAt_of_hardcore` (`Sharp/Graham.lean`) | — |
| Lemma 3.10 | minimal $\ge 4$-alphabets | ✓ | ✓ | `sharp_of_minimal` (`Sharp/Graham.lean`) | — |
| SHARP Cases D/P/L/E | all-$M$ constructions | ✓ | corrob. | `caseD/caseP/caseL/caseE` (`Sharp/Case*.lean`) | — |
| SHARP Case T | finite exceptional lines | ✓ (reach + slope) | ✓ | `caseT` (`Sharp/CaseT*.lean`) | Table A (+suppl.) |
| SHARP Case B | finite base classes + descent | ✓ (descent) | ✓ | `caseB` (`Sharp/CaseB.lean`) | Table B |
| Theorem 3 (SHARP) | finite additive lemma | ✓ + finite | ✓ | `sharp` (`Sharp/Main.lean`) | Tables A/B |
| Main Theorem | assembly (Parts I–IV) | ✓ | — | `erdos_1112` (`Final.lean`) | — |

---



---
**Next ▶** [Part I — Existence](01-existence.md) · **Statement in Lean:** [`lean/Erdos1112.lean`](../lean/Erdos1112.lean)
