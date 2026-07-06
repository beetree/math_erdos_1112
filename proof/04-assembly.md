*Erdős #1112 · [Index](../README.md) · Part IV of IV*

## Part IV. Assembly

**Proof of the Main Theorem.** ([`Final.lean`](../lean/Erdos1112Proof/Final.lean)) Part 1 is Theorem 1. For Part 2, let $d_2 \le k$, $k \ge 3$, and
let $(r_i)$ be any prescribed growth sequence; build the certificate $B$ of Lemma 2.1. Let $A$ be
any $(d_1, d_2)$-sequence, $G_\infty$ its tail alphabet, $g := \gcd(G_\infty)$:

| Case | Handled by |
|---|---|
| $|G_\infty/g| = 1$ | Lemma 2.3 (AP tail) |
| $|G_\infty/g| = 2$, word eventually periodic | Lemma 2.5 |
| $|G_\infty/g| = 2$, some $W_2(\sigma_0) \ge 2$, $k$ odd or $d_2 \le k-1$ | Lemmas 2.8(a) + 2.7 |
| $|G_\infty/g| = 2$, some $W_2(\sigma_0) \ge 2$, $k$ even, $d_2 = k$ | Lemma 2.8(a) boundary routing: eventually periodic → 2.5; some balanced tail → 2.8(b) on the tail (2.5 or 2.10); every tail unbalanced → 2.9 + 2.7 |
| $|G_\infty/g| = 2$, all $W_2 \le 1$ (balanced) | Lemma 2.8(b): Morse–Hedlund → Lemma 2.5 or 2.10 |
| $|G_\infty/g| \ge 3$ | Lemma 2.12 (Slot Lemma) with $m(G_\infty/g) \le \max(G_\infty/g) - 1 \le d_2 - 1 \le k - 1$ by **Theorem 3 (SHARP)** |

In every case $kA$ is tail-covering (mod $g \cdot m'$ after Lemma 2.4), so $B$ meets $kA$. Since
$(r_i)$ was arbitrary, non-existence holds in the strong form. $\blacksquare$

**Case coverage within Theorem 3** (the hard-core decision tree): the six cases of §III.9
partition the hard core — D and P are disjoint lines; $e = h$ triples with $a \mid b + M$ would
need $a \mid 3e$, possible only for $a = 3, e = 1$, i.e. $(3,4,5)$, where both Lemma 3.12
(witness $(2,1,1)$) and Lemma 3.15 apply; every remaining triple has $\eta \notin \{0, 1, a-1\}$
and falls to exactly one of E / T / B by the sizes of $a$ and $\mu$. All boundary sub-splits are
internal to their lemmas (P: the pair-frame Lemma 3.12 for $r = 3, 4$ and the three $r = 5$ corner
triples, the box Lemma 3.14 for $M \ge 2a+4$; L: parity of $a$ and $g = 1$ vs $g \ge 2$; D: a
single uniform construction, cf. the Case-D remark).

---



---
◀ [Part III — the (SHARP) lemma](03-sharp.md) · **Next ▶** [Appendix A — Verification](appendix-A-verification.md)
**Formalized in:** [`lean/Erdos1112Proof/Final.lean`](../lean/Erdos1112Proof/Final.lean) (the three theorems, stated directly against the frozen definitions and proved from `namespace Erdos1112.Proof`).
