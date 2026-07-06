*Erdős #1112 · [Index](../README.md) · Part II of IV*

## Part II. Non-existence for $d_2 \le k$: reduction to (SHARP)

Throughout Part II, $k \ge 3$ and $d_2 \le k$.

### II.1 The certificate

**Lemma 2.1 (certificate).** ([`NonEx/Certificate.lean`](../lean/Erdos1112Proof/NonEx/Certificate.lean)) *Fix any enumeration $(m_i, \rho_i)$ of all pairs
$\{(m, \rho) : m \ge 1,\ 0 \le \rho < m\}$ in which each pair occurs infinitely often. Given any
prescribed $r_1 \le r_2 \le \cdots$, choose inductively $b_i :=$ the least integer
$> \max(r_i b_{i-1},\ b_{i-1},\ i)$ congruent to $\rho_i \bmod m_i$. If every $(d_1,d_2)$-sequence
$A$ is tail-covering, then this single $B$ defeats them all: for any $A$ pick $(m, \rho, X_0)$
with $kA \supseteq \{x \ge X_0 : x \equiv \rho \pmod m\}$ and an index $i$ with
$(m_i, \rho_i) = (m, \rho)$ and $b_i \ge X_0$; then $b_i \in kA$.* $\square$

So it suffices to prove: **every $(d_1,d_2)$-sequence with $d_2 \le k$ is tail-covering.** (Full
congruence-class tails are genuinely needed here: the class modulus can exceed $d_2$ — e.g. gaps
$3,5,3,5,\dots$ with $k = 5$ give exactly the six classes $5a_1 + \{0,1,3,4,6,7\} \bmod 8$.)

### II.2 Reductions

**Lemma 2.2 (tail).** ([`NonEx/Kit.lean`](../lean/Erdos1112Proof/NonEx/Kit.lean)) Let $T$ be an index past which all gaps lie in $G_\infty$. Since
$kA \supseteq$ ($k$-fold sums of $A \cap [a_T, \infty)$), it suffices to treat the tail; we do so
silently from now on.

**Lemma 2.3 (one letter).** ([`NonEx/GapWord.lean`](../lean/Erdos1112Proof/NonEx/GapWord.lean)) If $G_\infty = \{\delta\}$, the tail is an AP and
$kA \supseteq \{k a_T + \delta j : j \ge 0\}$: tail-covering with $m = \delta$. $\square$

**Lemma 2.4 (rescaling).** If $g := \gcd(G_\infty) > 1$, write the tail as $a_T + g A'$ where
$A'$ has gap alphabet $G_\infty/g$ with gcd $1$ and max $\le d_2/g$. If the $k$-fold sums of $A'$
are tail-covering mod $m'$, then $kA$ is tail-covering mod $g m'$. So we may assume
$\gcd(G_\infty) = 1$. $\square$

**Lemma 2.5 (eventually periodic).** ([`NonEx/GapWord.lean`](../lean/Erdos1112Proof/NonEx/GapWord.lean)) If the gap word is eventually periodic, the tail of $A$ is a
full pattern $(C + P\mathbb{Z}) \cap [T', \infty)$ for a finite $C$ and period-sum $P$; then $kA$
contains, for each $k$-multiset of $C$ with sum $\sigma$, the full class tail $\sigma +
P\mathbb{Z}$: tail-covering. $\square$

### II.3 The two-letter core

Assume now $G_\infty = \{\delta < \delta'\}$, $\gcd(\delta, \delta') = 1$ (Lemma 2.4),
$e := \delta' - \delta \ge 1$, both letters infinitely often. The two gap values are $\delta$ and
$\delta' = \delta + e$; since every gap of $A$ lies in $[d_1, d_2]$ and $d_2 \le k$ here, the
larger letter satisfies $\delta' = \delta + e \le d_2 \le k$ (the tail alphabet need **not**
attain $d_2$; we only use the inequality $\delta + e \le k$ below). Gaps are
$g_n = \delta + e h_n$ with $h_n \in \{0,1\}$; $q_n := h_1 + \cdots + h_n$. Every
$x \in kA - k a_1$ has the form $x = \delta s + e w$ with $s = \sum_t i_t$, $w = \sum_t q_{i_t}$.

**Lemma 2.6 (interval property).** ([`NonEx/TwoLetter/Core.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Core.lean)) *For each $s$, $W_s := \{\sum_t q_{i_t} : \sum_t i_t = s\}$ is
a full integer interval $[w^-(s), w^+(s)]$, and $w^\pm(s+1) - w^\pm(s) \in \{0, 1\}$.*
*Proof.* The set of $k$-multisets of nonnegative integers with fixed sum $s$ is connected under
moves $(i_a, i_b) \to (i_a - 1, i_b + 1)$, and each move changes $\sum q$ by
$h_{i_b + 1} - h_{i_a} \in \{-1, 0, 1\}$; a path from a minimizer to a maximizer visits a set of
integer values with no gap $\ge 2$. $\square$

**Lemma 2.7 (sweep).** ([`NonEx/TwoLetter/Core.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Core.lean)) *If $w^+(s) - w^-(s) \ge d_2 - 1$ for all $s \ge S_0$, then $kA - k a_1$
contains all sufficiently large integers (so $kA$ is tail-covering with $m = 1$).*
*Proof.* Given large $x$, representations $x = \delta s + e w$ require
$s \equiv x \delta^{-1} \pmod e$; admissible $s$ form an AP of difference $e$, and
$w(s) := (x - \delta s)/e$ increases by exactly $\delta$ when $s$ decreases by $e$. The windows
$[w^-(s), w^+(s)]$ are nondecreasing in $s$ with increments in $[0, e]$ per admissible step. For
the largest admissible $s$ with $w(s) \ge 0$ we have $w(s) < \delta \le w^+(s)$; for small
admissible $s$, $w(s) > w^+(s)$. If no admissible $s \ge S_0$ had $w(s) \in [w^-(s), w^+(s)]$,
there would be a crossing pair $s' < s' + e$ with $w(s'+e) < w^-(s'+e)$ and $w(s') > w^+(s')$;
then $w^+(s') < w(s') = w(s'+e) + \delta \le w^-(s'+e) - 1 + \delta \le w^-(s') + e - 1 + \delta$,
i.e. $w^+(s') - w^-(s') \le (\delta + e) - 2 = \delta' - 2 \le d_2 - 2$, a contradiction (the
hypothesis width $\ge d_2 - 1 \ge \delta' - 1$ is what is used). By Lemma 2.6 the landed value is
attained.
$\square$

**Lemma 2.8 (width dichotomy).** ([`NonEx/TwoLetter/Core.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Core.lean), [`NonEx/TwoLetter/Balanced.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Balanced.lean)) Let $W_2(\sigma) := \max\{q_i + q_j : i + j = \sigma\} -
\min\{q_i + q_j : i + j = \sigma\}$.

*(a)* Suppose $W_2(\sigma_0) \ge 2$ for some $\sigma_0$. Disjoint index-pairs placed on
antidiagonals contribute widths additively. Then:
- **$k$ odd:** $(k-1)/2$ pairs at $\sigma_0$ plus one leftover index give
  $w^+(s) - w^-(s) \ge k - 1 \ge d_2 - 1$ for all $s \ge \tfrac{k-1}2 \sigma_0$, using exactly
  $k$ indices.
- **$k$ even, $d_2 \le k-1$:** $(k/2 - 1)$ pairs at $\sigma_0$ plus one free pair at
  $\tau := s - (k/2 - 1)\sigma_0$ give width $\ge (k-2) + W_2(\tau) \ge k - 2 \ge d_2 - 1$.
- **$k$ even, $d_2 = k$ (boundary):** three possibilities, exhaustively routed. If the gap word
  is eventually periodic, Lemma 2.5 applies. Otherwise, if some tail of the gap word is balanced,
  pass to that tail (Lemma 2.2) and apply the Morse–Hedlund dichotomy exactly as in part (b)
  below: the tail is ultimately periodic (Lemma 2.5) or Sturmian (Lemma 2.10), and either way
  $kA$ is tail-covering with no width argument needed. Otherwise **every** tail of the gap word
  is unbalanced, and Lemma 2.9 (whose hypotheses — $W_2(\sigma_0) \ge 2$, non-periodicity,
  every-tail-unbalancedness — are exactly the ones in force on this branch) supplies width
  $\ge k - 1$ for all large $s$.

In every branch that ends with a width bound, Lemma 2.7 then gives tail-covering; the remaining
branches conclude directly via Lemma 2.5 or Lemma 2.10. *(The even-$k$ parity split is essential:
$\lfloor k/2 \rfloor$ pairs plus a leftover would use $k+1$ indices when $k$ is even.)*

*(b)* Otherwise $W_2(\sigma) \le 1$ for all $\sigma$. For any equal-length windows $(i, i']$ and
$(j', j]$ one has $i + j = i' + j'$, so
$|(q_{i'} - q_i) - (q_j - q_{j'})| = |q_{i'} + q_{j'} - q_i - q_j| \le 1$: the word $h$ is
**balanced**. A balanced one-sided infinite word is either ultimately periodic (Lemma 2.5) or
mechanical with irrational slope, $q_n = \lfloor n\alpha + \beta \rfloor$ after passing to a tail
(Lemma 2.2), and the Sturmian case is Lemma 2.10. We do **not** invoke this as a black box:
Proposition 2.8′ gives a self-contained, density-free proof of exactly the direction used (the
classical statement is [MH40]; see also [Lo, Ch. 2]). $\square$

**Proposition 2.8′ (density-free balanced classification).** ([`NonEx/TwoLetter/MH/Slope.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/MH/Slope.lean)) *A balanced word $h : \mathbb{N} \to
\{0,1\}$ with $q_n := h_1 + \cdots + h_n$ is either eventually periodic, or — after passing to a
tail — satisfies $q_n = \lfloor n\alpha + \beta \rfloor$ for some irrational $\alpha \in (0,1)$ and
$\beta \in \mathbb{R}$. The only analytic input is Dirichlet's approximation theorem; no density,
equidistribution, three-distance, or Morse–Hedlund citation is used.*

*Proof.* Set $\alpha := \sup_{n \ge 1}(q_n - 1)/n$ and $D_n := q_n - n\alpha$ (so $D_0 = 0$). The
balance hypothesis yields both the two-sided bound $|D_n| \le 1$ and the one-sided *oscillation*
bound $D_m - D_n \le 1$: the latter by transferring the balance inequality along the progression
$n, n + \Delta, n + 2\Delta, \dots$ with $\Delta := |m - n|$, where each step changes the
discrepancy by a fixed increment, and iterating until the accumulated increment would violate
$|D| \le 1$ — which pins the increment's sign and gives the bound. Also $\alpha \in [0,1]$ (from
$0 \le q_n \le n$). Two cases:

- *$\alpha$ rational*, $\alpha = p/q$ in lowest terms: then $q\,D_n = q\,q_n - p\,n$ is an integer
  confined to $[-q, q]$, and balance makes it eventually monotone, hence eventually constant; so
  $h$ is eventually periodic (period $q$). ([`NonEx/TwoLetter/MH/RationalCase.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/MH/RationalCase.lean))
- *$\alpha$ irrational*: the two bounds force $q_n = \lfloor n\alpha + \beta \rfloor$ for a suitable
  intercept $\beta$ (the supremum of the fractional parts $\{n\alpha\}$ over the indices where
  $q_n$ increments, as constructed in `mechanical_tail`). The floor identity can fail at most at
  the single index with $\{n\alpha + \beta\} = 0$, which is unique because $\alpha$ is irrational;
  a tail beyond it is mechanical everywhere. Irrationality also excludes $\alpha \in \{0,1\}$, so
  $\alpha \in (0,1)$ ([`NonEx/TwoLetter/MH/IrrationalCase.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/MH/IrrationalCase.lean)). $\square$

The threshold separation comes from the discrepancy *oscillation* bound, not from any density or
equidistribution statement. Similarly, the uniform syndeticity used in Lemma 2.10 (Step 1) is
obtained from a single Dirichlet approximation (a bounded circle walk), not the three-distance
theorem. This is the route carried out in the formalization (`disc_osc_le_one`, `mechanical_tail`,
`walk_enters`; Appendix D).

**Lemma 2.9 (boundary width; $k$ even $\ge 4$).** ([`NonEx/TwoLetter/Core.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Core.lean)) *Let $h$ use both letters infinitely often,
$W_2(\sigma_0) \ge 2$ for some $\sigma_0$, $h$ not eventually periodic, and suppose every tail of
$h$ is unbalanced. Then $w^+(s) - w^-(s) \ge k - 1$ for all sufficiently large $s$.*

*Proof.* Every-tail-unbalancedness gives $W_2(\sigma) \ge 2$ for infinitely many $\sigma$; fix two
of them $\sigma_0 < \sigma_1$, $\Delta := \sigma_1 - \sigma_0$. For large $s$ consider two
configuration families, each using exactly $k$ indices:
(1) $(k/2 - 1)$ extremal pairs at $\sigma_0$ + one free pair at $\tau := s - (k/2-1)\sigma_0$,
giving width $\ge (k-2) + W_2(\tau)$;
(2) $(k/2 - 2)$ extremal pairs at $\sigma_0$ + one extremal pair at $\sigma_1$ + one free pair at
$\tau - \Delta$, giving width $\ge (k-2) + W_2(\tau - \Delta)$ (here $k/2 - 2 \ge 0$ uses
$k \ge 4$).
If $w^+(s) - w^-(s) \le k-2$, both force $W_2(\tau) = W_2(\tau - \Delta) = 0$. But
$W_2(\tau) = 0$ means $q_i + q_{\tau - i}$ is constant, i.e. $h_{i+1} = h_{\tau - i}$ for
$0 \le i \le \tau - 1$: the prefix $h[1..\tau]$ is a palindrome; likewise $h[1..\tau-\Delta]$. A
palindromic prefix of a palindrome is also its suffix, i.e. $h[1..\tau-\Delta]$ is a border of
$h[1..\tau]$, so $h[1..\tau]$ has period $\Delta$ (the classical border–period duality; Lothaire
Ch. 1). If the width bound failed at infinitely many $s$ then — $\Delta$ being fixed and
$\tau(s)$ strictly increasing — $h$ would have period $\Delta$, contradicting non-periodicity.
$\square$

**Lemma 2.10 (Sturmian case).** ([`NonEx/TwoLetter/Sturmian.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/Sturmian.lean)) *Let the two-letter tail (§II.3) have $q_n = \lfloor n\alpha +
\beta \rfloor$ for an irrational $\alpha \in (0,1)$ and some $\beta \in \mathbb{R}$. Then
$kA - k a_1$ contains all sufficiently large integers, so $kA$ is tail-covering with $m = 1$.*

We keep the notation of §II.3: gaps are $g_n = \delta + e\,h_n$ with $h_n \in \{0,1\}$,
$e = \delta' - \delta \ge 1$, $\gcd(\delta, e) = 1$, $q_n = h_1 + \cdots + h_n$, and
$\delta' = \delta + e \le d_2 \le k$. Every $x \in kA - ka_1$ has the form $x = \delta s + e w$ with
$s = \sum_t i_t$ (all $i_t \ge 1$, working in the tail) and $w = \sum_t q_{i_t}$, so
$w \in W_s := \{\sum_t q_{i_t} : i_t \ge 1,\ \sum_t i_t = s\}$.

**Step 0 (the window that carries $W_s$).** Since $q_n = n\alpha + \beta - \{n\alpha + \beta\}$,
$$\sum_t q_{i_t} = \Big(\alpha \sum_t i_t + k\beta\Big) - \sum_t \{i_t\alpha + \beta\}
= X_s - \sum_t \{i_t\alpha + \beta\}, \qquad X_s := s\alpha + k\beta.$$
Each $\{i_t\alpha + \beta\} \in [0,1)$, so $\sum_t \{i_t\alpha + \beta\} \in [0, k)$ and hence
$$W_s \subseteq (X_s - k,\ X_s] \cap \mathbb{Z}. \tag{2.10.1}$$

**Step 1 (uniform syndeticity).** ([`NonEx/TwoLetter/MH/Walk.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/MH/Walk.lean)) *For every arc $J = (u, v) \subseteq (0,1)$ with $v - u > 0$
there is an integer $L = L(v-u)$, depending only on $\alpha$ and the length $v - u$ (not on the
position of $J$ nor on $\beta$), such that every block of $L$ consecutive integers
$\{N+1, \dots, N+L\}$ contains some $n$ with $\{n\alpha + \beta\} \in J$.* Indeed the rotation
$R_\alpha : t \mapsto t + \alpha \bmod 1$ is minimal ($\alpha$ irrational), hence uniformly
recurrent: the return-time set $\{n \ge 1 : \{n\alpha + \beta\} \in J\}$ is syndetic with gaps
bounded by a value $L(v-u)$ depending only on $\alpha$ and the length $v - u$, uniformly in the
phase $\beta$. This is the general fact that irrational rotations have uniformly bounded return
gaps for arcs of fixed positive length; the three-distance (Steinhaus) theorem suffices for it:
pick $N = N(\alpha, v-u)$ so that the partition of the circle by the points $\{\alpha\},
\{2\alpha\}, \dots, \{N\alpha\}$ has every arc of length $< v - u$ (possible since
$\{n\alpha\}_{n \ge 1}$ is dense, so the maximal arc length tends to $0$ as $N \to \infty$).
For any $n_0 \ge 0$ the $N$ points $\{n\alpha + \beta\}$ with $n_0 < n \le n_0 + N$ form a
rotate of that partition's point set (by $n_0\alpha + \beta$), so every arc of length $\ge v-u$
— in particular $J$, wherever it sits — contains at least one of them. Thus $L := N$ works.
Fix this $L$ for the specific arc used below.

**Remark (three-distance is avoidable, verified formally).** The formalization discharges Step 1
without the three-distance theorem, by an explicit Dirichlet-step circle walk: one application of
Dirichlet's approximation theorem (plus a sign flip) produces a single *positive* rotation step
$\theta < \varepsilon/2$, nonzero by irrationality, and the orbit $x_{m+1} = \{x_m + \theta\}$
provably enters any arc of length $\varepsilon$ within $2\lceil 2/\theta \rceil + 2$ steps (it
climbs by $+\theta$ and must wrap within $\lceil 1/\theta \rceil$ steps, landing in $[0,\theta)$).
This gives the same $\beta$-uniform bound $L(v-u)$ more elementarily than minimality/uniform
recurrence. See Appendix D.

**Step 2 (sub-window claim).** ([`NonEx/TwoLetter/MH/Subwindow.lean`](../lean/Erdos1112Proof/NonEx/TwoLetter/MH/Subwindow.lean)) *Fix $\eta \in (0, \tfrac12)$. There is $S_0 = S_0(\eta, \alpha,
\beta, k)$ such that for every $s \ge S_0$, $W_s$ contains every integer $w$ for which*
$$\theta := X_s - w \in [\eta,\ k - \eta]. \tag{2.10.2}$$
That is: within the real window $(X_s - k, X_s]$ of (2.10.1), the integer points whose distance
$\theta$ below $X_s$ lies in $[\eta, k-\eta]$ are all attained.

*Proof of Step 2.* Fix $s \ge S_0$ and an integer $w$ with $\theta \in [\eta, k-\eta]$. We
produce indices $i_1, \dots, i_k \ge 1$, pairwise distinct, with
$$\sum_{t=1}^k i_t = s \quad\text{and}\quad \sum_{t=1}^k \{i_t\alpha + \beta\} = \theta
\ \ \text{exactly}, \tag{2.10.3}$$
which by Step 0 gives $\sum_t q_{i_t} = X_s - \theta = w$, i.e. $w \in W_s$.

Set $\kappa := \eta/4$. Consider the open interval
$$\mathcal{I} := \big(\max(0, \theta - 1) + \kappa,\ \min(k-1, \theta) - \kappa\big).$$
*It is nonempty, with $|\mathcal{I}| \ge \eta/2$, in each of the three regimes of $\theta$:*
- $\eta \le \theta \le 1$: then $\max(0,\theta-1) = 0$ and $\min(k-1,\theta) = \theta$ (as
  $\theta \le 1 \le k-1$), so $|\mathcal{I}| = \theta - 2\kappa \ge \eta - \eta/2 = \eta/2$.
- $1 < \theta \le k-1$: then $|\mathcal{I}| = \theta - (\theta - 1) - 2\kappa = 1 - \eta/2 >
  \eta/2$.
- $k-1 < \theta \le k - \eta$: then $\min(k-1,\theta) = k-1$, so
  $|\mathcal{I}| = (k-1) - (\theta - 1) - 2\kappa = (k - \theta) - 2\kappa \ge \eta - \eta/2
  = \eta/2$.

Pick any $T^* \in \mathcal{I}$ and set the target arc
$$J := \Big(\tfrac{T^*}{k-1} - \tfrac{\kappa}{k-1},\ \tfrac{T^*}{k-1} + \tfrac{\kappa}{k-1}\Big)
\subseteq (0,1),$$
which is nonempty of length $2\kappa/(k-1) > 0$; let $L = L\big(2\kappa/(k-1)\big)$ be its
syndeticity constant from Step 1. We choose the $k-1$ *free* indices
$i_1 < i_2 < \cdots < i_{k-1}$, all with $\{i_t\alpha + \beta\} \in J$, from the **lowest**
available blocks: for $j = 1, \dots, k-1$, the block $B_j := \{(j-1)L + 1, \dots, jL\}$ contains
(Step 1) at least one index $i_j$ with $\{i_j\alpha + \beta\} \in J$; pick one such $i_j$ per
block. These lie in disjoint blocks, so $i_1 < \cdots < i_{k-1}$ are distinct, and
$$i_j \le jL, \qquad \sum_{t=1}^{k-1} i_t \le L\,(1 + 2 + \cdots + (k-1)) = L\tfrac{k(k-1)}{2},
\qquad i_{k-1} \le (k-1)L. \tag{2.10.4}$$
Define the threshold
$$S_0 := 1 + L\,(k-1)\Big(\tfrac{k}{2} + 1\Big), \tag{2.10.5}$$
an integer once $L$ is (it always is; round up if needed). Assume $s \ge S_0$ from now on. Set the
forced last index
$$i_k := s - \sum_{t=1}^{k-1} i_t.$$
Then, using (2.10.4) and (2.10.5),
$$i_k \;\ge\; s - L\tfrac{k(k-1)}{2} \;\ge\; S_0 - L\tfrac{k(k-1)}{2} \;=\; 1 + (k-1)L \;>\;
(k-1)L \;\ge\; i_{k-1},$$
so $i_k \ge 1$, and $i_k > i_{k-1} \ge \cdots \ge i_1$, i.e. $i_k$ is distinct from all free
indices. Thus $i_1, \dots, i_k \ge 1$ are pairwise distinct with $\sum_t i_t = s$.

With these choices,
$$F := \sum_{t=1}^{k-1} \{i_t\alpha + \beta\} \in \big((k-1)(\tfrac{T^*}{k-1} - \tfrac{\kappa}{k-1}),\ 
(k-1)(\tfrac{T^*}{k-1} + \tfrac{\kappa}{k-1})\big) = (T^* - \kappa,\ T^* + \kappa)
\subseteq \big(\max(0,\theta-1),\ \min(k-1,\theta)\big), \tag{2.10.6}$$
the last inclusion because $T^* \in \mathcal{I}$ sits at distance $> \kappa$ from each endpoint of
$\big(\max(0,\theta-1),\ \min(k-1,\theta)\big)$.

It remains to verify (2.10.3). By construction $\sum_{t\le k} i_t = s$. For the fractional sum,
write $\Theta := \sum_{t\le k} \{i_t\alpha + \beta\} = F + \{i_k\alpha + \beta\}$. From (2.10.6)
and $\{i_k\alpha + \beta\} \in [0,1)$,
$$\Theta > \max(0,\theta - 1) + 0 \ge \theta - 1, \qquad
\Theta < \min(k-1,\theta) + 1 \le \theta + 1,$$
so $\Theta \in (\theta - 1,\ \theta + 1)$. On the other hand,
$$\Theta = \sum_{t\le k}(i_t\alpha + \beta) - \sum_{t\le k}\lfloor i_t\alpha + \beta\rfloor
= X_s - \sum_{t\le k} q_{i_t} \in X_s - \mathbb{Z} = \theta + \mathbb{Z},$$
using $\sum_{t\le k}(i_t\alpha + \beta) = \alpha s + k\beta = X_s$ *exactly* and
$w = X_s - \theta \in \mathbb{Z}$. The unique element of the coset $\theta + \mathbb{Z}$ in the
open interval $(\theta - 1, \theta + 1)$ is $\theta$ itself, so $\Theta = \theta$. This proves
(2.10.3) and hence Step 2. $\square$

**Step 3 (the ladder lands in the sub-window).** Instantiate Step 2 with the specific choice
$$\eta := \tfrac14 \min(\alpha,\ 1 - \alpha) \in (0, \tfrac18], \tag{2.10.7}$$
and fix the resulting $S_0$. Let $x$ be a large integer. Because $\gcd(\delta, e) = 1$, the
equation $x = \delta s + e w$ in nonnegative integers has, for each residue of $s$, at most one
$w$; the admissible values of $s$ are exactly those with
$$s \equiv x\,\delta^{-1} \pmod e, \tag{2.10.8}$$
an arithmetic progression of common difference $e$, and for each such $s$ we set
$w(s) := (x - \delta s)/e \in \mathbb{Z}$. Define
$$\theta(s) := X_s - w(s) = \Big(s\alpha + k\beta\Big) - \frac{x - \delta s}{e}.$$
As $s$ increases by one admissible step (i.e. $s \mapsto s + e$), $X_s$ increases by $e\alpha$ and
$w(s)$ decreases by $\delta$, so
$$\theta(s + e) - \theta(s) = e\alpha + \delta =: \gamma > 0. \tag{2.10.9}$$
Thus, along the admissible progression, $\theta$ is a strictly increasing arithmetic sequence of
common difference exactly $\gamma$.

*The step is shorter than the sub-window.* The sub-window (2.10.2) is the real interval
$\theta \in [\eta, k-\eta]$, of length $k - 2\eta$. Using $\delta + e = \delta' \le k$ and (2.10.7),
$$\gamma = \delta + e\alpha = (\delta + e) - e(1 - \alpha) = \delta' - e(1-\alpha)
\le k - (1 - \alpha), \tag{2.10.10}$$
where the last step uses $e \ge 1$ and $1 - \alpha > 0$. Since
$2\eta \le \tfrac12(1 - \alpha) < 1 - \alpha$, we get
$$\gamma \le k - (1-\alpha) < k - 2\eta, \tag{2.10.11}$$
i.e. the ladder step $\gamma$ is **strictly** smaller than the sub-window length $k - 2\eta$.

*Landing.* A strictly increasing arithmetic sequence $\{\theta(s)\}$ with common difference
$\gamma$ cannot skip over a real interval of length $> \gamma$: if $\theta(s) < \eta$ and
$\theta(s + e) > k - \eta$ for two consecutive admissible terms, then
$\gamma = \theta(s+e) - \theta(s) > (k - \eta) - \eta = k - 2\eta$, contradicting (2.10.11).
For $x$ large the sequence $\theta(s)$ ranges from very negative (at the smallest admissible
$s \ge S_0$, where $w(s) \approx x/e$ dominates) to arbitrarily large (as $s \to x/\delta$), so it
increases across $[\eta, k-\eta]$; by the no-skip property some admissible $s^\ast \ge S_0$ has
$\theta(s^\ast) \in [\eta, k - \eta]$. (Concretely "$x$ large" is two explicit thresholds, made
separate in the formalization: one lower bound on $x$ forces the landing index $s^\ast \ge S_0$
so that Step 2 applies, and a second forces $w(s^\ast) \ge 0$ so that the representation
$x = \delta s^\ast + e\,w(s^\ast)$ uses a nonnegative $w$; $X_0$ is their maximum plus a constant.)
Step 2 then gives $w(s^\ast) \in W_{s^\ast}$, whence
$$x = \delta s^\ast + e\,w(s^\ast) \in kA - k a_1.$$
As $x$ was an arbitrary large integer, $kA - k a_1 \supseteq$ all large integers; in the original
(unscaled) coordinates this is a full congruence-class tail mod $g$, so $kA$ is tail-covering.
$\square$

*Verification (redundant; confirms the threshold structure of Step 2).* The sub-window claim was
checked by exact bitmask computation of $W_s$ for $\alpha \in \{\tfrac{\sqrt5-1}{2},\ \sqrt2 - 1,\
0.7548776662\}$, $\beta = 0.3$, $k \in \{3,4,5\}$: for each $(\alpha, k)$ every integer $w$ with
$\theta \in [\eta, k-\eta]$ (with $\eta$ as in (2.10.7)) lies in $W_s$ for all $s$ beyond a finite
threshold. The last violating $s$ observed (with **no** violation for any larger $s$ up to
$s = 900$) was: at $k=3$, $s = 21$ (golden), $15$ ($\sqrt2-1$), $57$ ($0.7549$); at $k=4$,
$s = 61, 24, 99$; at $k=5$, $s = 88, 57, 141$. This is exactly the "$s \ge S_0$" form of Step 2 (the finitely
many small-$s$ exceptions lie below $S_0$ and are irrelevant, since Step 3 uses only large $s$).
The end-to-end coverage was also confirmed directly: for gaps $\{2,3\}$ (so $\delta = 2$, $e = 1$,
$d_2 = 3$) at the boundary $k = 3 = d_2$, with $h$ the golden Sturmian word, the $3$-fold sumset
$3A - 3a_1$ was computed to contain **every** integer in the interior window $[2000,\ 10472)$
(zero omissions).

**Theorem 2 (two-letter core; and consecutive windows).** *Let $k \ge 3$ and $d_2 \le k$. Every
$(d_1,d_2)$-sequence whose tail alphabet has $\le 2$ letters is tail-covering. In particular
(with Lemma 2.1) $r_k(d_1, d_1+1)$ does not exist for $d_1 + 1 \le k$, in the strong form.*
*Proof.* Lemmas 2.3–2.5, 2.8 (with 2.9 at the even boundary), 2.10 exhaust the cases. $\square$

### II.4 Three or more letters: widths are not the obstacle

**Lemma 2.11.** *For a tail alphabet with $\ge 3$ letters (rescaled, gcd 1), $W_2(\sigma) \le 1$
for all $\sigma$ is impossible; moreover every tail of the gap word is unbalanced (it contains,
beyond any point, two single-letter windows differing by $\ge 2$). Hence by Lemma 2.8(a) — with
Lemma 2.9 at the even boundary $d_2 = k$, whose proof is alphabet-agnostic — the antidiagonal
width hypothesis of Lemma 2.7 holds for all large $s$ unless the word is eventually periodic
(Lemma 2.5).* $\square$

For $\ge 3$ letters, however, Lemma 2.6 fails (configuration moves change values by letter
*differences*, which can exceed 1), so Lemma 2.7 does not apply directly: $W_s$ is dense in its
span but may have holes. The route below bypasses the antidiagonal analysis entirely.

### II.5 The Slot Lemma: reduction to a finite subset-sum problem

**Lemma 2.12 (Slot Lemma).** ([`NonEx/SlotLemma.lean`](../lean/Erdos1112Proof/NonEx/SlotLemma.lean), [`NonEx/SlotLemmaParts.lean`](../lean/Erdos1112Proof/NonEx/SlotLemmaParts.lean)) *Let $A$ have tail alphabet $G_\infty$, $|G_\infty| \ge 3$,
$\gcd(G_\infty) = 1$ (after Lemma 2.4), $M := \max G_\infty \le d_2$. If $k - 1 \ge m(G_\infty)$,
then $kA$ is tail-covering.*

*Proof.* Let $S$ realize $m(G_\infty)$: a multiset with $|S| = m \le k-1$ whose subset sums
contain $\{c, c+1, \dots, c+M-1\}$. Enumerate $S = \{\delta_1, \dots, \delta_m\}$ (values in
$G_\infty$, repeats allowed). Because each value occurs infinitely often in the gap sequence, pick
$m$ distinct, pairwise non-adjacent positions $n_1, \dots, n_m$ with $g_{n_t} = \delta_t$. A
"fine slot" $t$ is a summand index $i_t \in \{n_t - 1,\ n_t\}$, contributing $p_{n_t - 1}$ ("off")
or $p_{n_t-1} + \delta_t$ ("on"). Over all on/off choices, the $m$ fine slots contribute
$\text{base} + \text{subset-sums}(S) \supseteq \text{base} + [c,\ c + M - 1]$, where
$\text{base} = \sum_t p_{n_t - 1}$. Park the remaining $k - 1 - m$ summands at fixed indices
(folding their contribution into $\text{base}$; repeated indices are allowed in $kA$). This uses
$k-1$ of the $k$ summands and realizes every value of an interval of $M$ consecutive integers.
The last summand $p_n$ is a coarse dial: in the tail, consecutive prefix sums differ by
$g_{n+1} \in G_\infty$, hence by $\le M$; so for any large $x$ the descending sequence
$x - \text{base} - p_n$ steps down by $\le M$ and cannot jump over an interval containing $M$
consecutive integers: some $n^*$ lands in it. Then $x \in kA - k a_1$. So $kA - k a_1 \supseteq$
all large integers (in rescaled coordinates; a full class tail mod $g$ in general). $\square$

The binding corner is $k = d_2 = M$ (the adversary uses the maximal gap infinitely often and $k$
is smallest): there $k - 1 \ge m(G_\infty)$ requires **exactly** $m(G_\infty) \le M - 1$. This is
what (SHARP) provides:

> **(SHARP).** For every finite $G \subset \mathbb{Z}_{\ge 1}$ with $|G| \ge 3$, $\gcd(G) = 1$,
> $\max(G) = M$: $\;m(G) \le M - 1$.

Indeed, given (SHARP): $k - 1 \ge d_2 - 1 \ge M - 1 \ge m(G_\infty)$ for all $k \ge d_2$ (and for
rescaled alphabets $M/g - 1 < d_2 - 1$ a fortiori). For perspective, a short self-contained bound
in the same direction (not needed below, but it shows the mechanism and handles all
$k \ge 2d_2 - 2$ by itself):

**Lemma 2.13 (base grid).** *If $G$ ($|G| \ge 3$, $\gcd G = 1$, $\min G = a$, $\max G = M$)
contains an element $c$ with $\gcd(a, c) = 1$, then $m(G) \le a + M - 1 \le 2M - 3$.*
*Proof.* Take $(a-1)$ copies of $c$ and $p := \lceil ((a-1)c + M - 1)/a \rceil$ copies of $a$.
For $n \in [(a-1)c,\ pa]$, the unique $i \in [0, a-1]$ with $ic \equiv n \pmod a$ has
$ic \le (a-1)c \le n$ and $(n - ic)/a \in [0, p]$; so the subset sums cover that interval, of
length $\ge M$. And $p \le M$, so the size is $\le a + M - 1$; $|G| \ge 3$ forces $a \le M-2$.
$\square$

**Conclusion of Part II.** ([`NonEx/Main.lean`](../lean/Erdos1112Proof/NonEx/Main.lean)) Modulo (SHARP) — proved in Part III — every $(d_1,d_2)$-sequence with
$d_2 \le k$, $k \ge 3$, is tail-covering: $\le 2$-letter tails by Theorem 2, $\ge 3$-letter tails
by Lemma 2.12 + (SHARP). With Lemma 2.1 this proves the Main Theorem's non-existence side, in the
strong form. $\square$

---



---
◀ [Part I — Existence](01-existence.md) · **Next ▶** [Part III — the (SHARP) lemma](03-sharp.md)
**Formalized in:** [`lean/Erdos1112Proof/NonEx/`](../lean/Erdos1112Proof/NonEx) (certificate, slot lemma, two-letter core, Sturmian/Morse–Hedlund).
