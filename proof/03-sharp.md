*Erdős #1112 · [Index](../README.md) · Part III of IV*

## Part III. The (SHARP) lemma: full proof

**Theorem 3 (SHARP).** ([`Sharp/Defs.lean`](../lean/Erdos1112Proof/Sharp/Defs.lean), [`SubsetSums.lean`](../lean/Erdos1112Proof/SubsetSums.lean), [`Basic.lean`](../lean/Erdos1112Proof/Basic.lean)) For every finite $G \subset \mathbb{Z}_{\ge 1}$ with $|G| \ge 3$,
$\gcd(G) = 1$, $\max(G) = M$: there is a multiset $S$ of elements of $G$ with $|S| \le M - 1$
whose subset sums contain $M$ consecutive integers.

*Trivial preliminaries.* If $a := \min G = 1$, take $M-1$ copies of $1$. Assume $a \ge 2$; the
hard core below will force $a \ge 3$.

### III.1 Machinery

**Lemma 3.1 (two-generator interval).** ([`Sharp/TwoGen.lean`](../lean/Erdos1112Proof/Sharp/TwoGen.lean)) *Let $\alpha < \beta$ be coprime positive integers,
$x \ge \beta - 1$, $y \ge \alpha - 1$. Then*
$$\{i\alpha + j\beta : 0 \le i \le x,\ 0 \le j \le y\} \supseteq [\,C,\ \alpha x + \beta y - C\,],
\qquad C := (\alpha - 1)(\beta - 1).$$
*Proof.* If $\alpha = 1$: $C = 0$; for $n \in [0, x + \beta y]$ take
$j := \min(y, \lfloor n/\beta \rfloor)$; then $0 \le n - j\beta \le \max(\beta - 1,\ n - y\beta)
\le x$. Let $\alpha \ge 2$. *Base case $y = \alpha - 1$:* for
$n \in [C,\ \alpha x + \beta(\alpha - 1) - C]$ pick the unique $j \in [0, \alpha - 1]$ with
$j\beta \equiv n \pmod\alpha$. Then $n - j\beta \ge C - (\alpha - 1)\beta = -(\alpha - 1)$, and
being $\equiv 0 \pmod \alpha$ it is $\ge 0$; and $i := (n - j\beta)/\alpha \le
(\alpha x + (\alpha - 1 - j)\beta - C)/\alpha \le x + (\alpha - 1)/\alpha$, so $i \le x$.
*Step $y \to y + 1$:* the new part of the interval is
$n \in (\alpha x + \beta y - C,\ \alpha x + \beta(y+1) - C]$; then $n - \beta \in
[C,\ \alpha x + \beta y - C]$ (the lower end because $\alpha x + \beta y \ge 2C + \beta$ for
$x \ge \beta - 1$, $y \ge \alpha - 1$, $\alpha \ge 2$), so by induction
$n - \beta = i\alpha + j\beta$ with $i \le x$, $j \le y$, and $n = i\alpha + (j+1)\beta$. $\square$

**Lemma 3.2 (frame lemma).** ([`Sharp/Frame.lean`](../lean/Erdos1112Proof/Sharp/Frame.lean)) *Let $g_1, g_2, \nu$ be positive integers and $L \ge 1$. Suppose for
every residue $\rho \in \mathbb{Z}_\nu$ there is a pair $(j_\rho, k_\rho)$ with
$0 \le j_\rho \le Y$, $0 \le k_\rho \le Z$ and $j_\rho g_1 + k_\rho g_2 \equiv \rho \pmod\nu$. Put
$S := \max_\rho (j_\rho g_1 + k_\rho g_2)$ and $x := \lceil (L - 1 + S)/\nu \rceil$. Then the
multiset $\{Y \times g_1,\ Z \times g_2,\ x \times \nu\}$, of size $Y + Z + x$, has subset sums
containing every integer of $[S,\ \nu x] \supseteq [S,\ S + L - 1]$.*
*Proof.* For $n \in [S, \nu x]$ let $\rho := n \bmod \nu$ and $r := j_\rho g_1 + k_\rho g_2 \le S
\le n$; $t := (n - r)/\nu$ is a nonnegative integer $\le x$. Take $j_\rho$ copies of $g_1$,
$k_\rho$ of $g_2$, $t$ of $\nu$. $\square$

In all uses below, $\nu = a \in G$, $(g_1, g_2) = (b, M)$, $L = M$; the **budget** of a box
$(Y, Z)$ is $B = \lceil (M - 1 + S)/a \rceil + Y + Z$ with $S$ the maximum over classes of the
*minimal* representative height in the box.

**Lemma 3.3 (staircase windows and merges).** ([`Sharp/Staircase.lean`](../lean/Erdos1112Proof/Sharp/Staircase.lean)) *Let $G = \{a, b, M\}$ with $\gcd(a, b) = 1$
(as always holds in the hard-core setting), $e := b - a$,
$\mu := M - a$, $g := \gcd(e, \mu)$, $e' := e/g$, $\mu' := \mu/g$ (coprime; $\mu' \ge 2$ since
$h := M - b \ge 1$), $C' := (e' - 1)(\mu' - 1)$. Note that $\gcd(a, b) = 1$ forces
$\gcd(a, g) = 1$, the form in which coprimality is used in part (d): a common prime of
$g = \gcd(e, \mu)$ and $a$ would divide $e$ and $a$, hence $b$, contradicting $\gcd(a, b) = 1$. Fix a multiset $(x, y, z)$ (copies of $a, b, M$)
with $y \ge \mu' - 1$, $z \ge e' - 1$, and set $c := y + z$, $V' := ye' + z\mu' - C'$. For
$0 \le t \le x + y + z$ the subset sums using exactly $t$ elements form $ta + \mathcal{O}_t$,
$\mathcal{O}_t = \{je + k\mu : j \le y,\ k \le z,\ \max(0, t - x) \le j + k \le t\}$, and:*

*(a) if $c \le t \le x$ then $\mathcal{O}_t \supseteq g\,[C', V']$;*

*(b) (two-frame merge, $g = 1$) if $x = c + 1$ and $V - C \ge a - 1$ (writing $V = V'$,
$C = C'$), the sums cover $[ca + C,\ (c+1)a + V]$, of length $a + (V - C) + 1$;*

*(c) (short two-frame merge, $g = 1$) if $x = c$, level $c + 1$ imposes only $j + k \ge 1$, which
excludes exactly the offset $0$; so $\mathcal{O}_{c+1} \supseteq [\max(C, 1),\ V]$, and if
$V \ge a + \max(C, 1) - 1$ the sums cover $[ca + C,\ (c+1)a + V]$, of length $a + V - C + 1$;*

*(d) ($g$-phase union, $g \ge 2$) if $x = c + g$ then all levels $t \in [c, c + g]$ satisfy (a);
since $\gcd(a, g) = 1$ (by the hypothesis $\gcd(a, b) = 1$, as noted above), each residue class
mod $g$ of the target is served by a unique $t_0 \in [c, c+g-1]$, and the sums cover the solid interval
$[\,(c+g-1)a + gC',\ ca + gV'\,]$, of length $g(V' - C') - (g-1)a + 1$ (the **base form**; it
uses one frame per class and needs no further hypothesis). More generally, if*
$$x \ge c + g \qquad\text{and}\qquad V' - C' \ge a - 1 \quad(\text{the frame-merge condition}),$$
*then within each residue class mod $g$ the frames $t_0, t_0 + g, t_0 + 2g, \dots$ ($\le x$) merge
and the sums cover the solid interval $[\,(c+g-1)a + gC',\ (x - g + 1)a + gV'\,]$ (the
**extended form**).*

*Remark (the merge condition is not removable from the extended form).* For $(a, b, M) =
(5, 7, 9)$ (so $e = 2$, $\mu = 4$, $g = 2$, $e' = 1$, $\mu' = 2$, $C' = 0$) with $y = 1$, $z = 0$
(so $c = 1$, $V' = 1$) and $x = 3 = c + g$, the merge condition fails ($V' - C' = 1 < 4 = a - 1$)
and so does the conclusion: the multiset $\{5, 5, 5, 7\}$ has subset sums
$\{0, 5, 7, 10, 12, 15, 17, 22\}$, which miss $11$ inside the would-be interval $[10, 12]$.

*Proof.* (a): for $t \in [c, x]$ every $(j, k)$ in the box has $j + k \le c \le t$ and
$i = t - j - k \in [0, x]$; apply Lemma 3.1 to $(e', \mu')$ and scale by $g$. (b): levels $c$,
$c+1$ cover $ta + [C, V]$; they merge iff $ca + V \ge (c+1)a + C - 1$. (c): every nonzero offset
of the box keeps all its representations at level $c+1$ (each has $j + k \ge 1$).

(d), *base form:* every $n$ in the displayed interval has $n \equiv t_0 a \pmod g$ for a unique
$t_0 \in [c, c+g-1]$, and $u := (n - t_0 a)/g$ satisfies $u \ge C'$ (from the left end, since
$t_0 \le c + g - 1$) and $u \le V'$ (from the right end, since $t_0 \ge c$); by (a), level $t_0$
realizes $t_0 a + g u = n$.

(d), *extended form (the merge step):* fix a residue class mod $g$ and its unique
$t_0 \in [c, c+g-1]$. The levels serving this class within $[c, x]$ are exactly the frames
$t_j := t_0 + jg$, $0 \le j \le J$, $J := \lfloor (x - t_0)/g \rfloor \ge 0$ (well-defined since
$t_0 \le c + g - 1 \le x - 1 < x$, using $x \ge c + g$), and by (a) frame $t_j$ covers
$t_j a + g\,[C', V']$ — an arithmetic progression of step $g$ inside the class
$t_0 a + g\mathbb{Z}$ (note $t_j a \equiv t_0 a \pmod g$). Two consecutive frames $t_j, t_{j+1}$
leave no gap of the class between them iff $t_{j+1} a + gC' \le t_j a + gV' + g$, i.e. iff
$g a + g C' \le g V' + g$, i.e. iff $V' - C' \ge a - 1$ — precisely the merge condition, under
which the class is covered solidly (in steps of $g$) on
$[\,t_0 a + gC',\ (t_0 + Jg)a + gV'\,]$; when $J = 0$ (a single frame) this holds trivially, with
no merging needed. Over $t_0 \in [c, c+g-1]$ the left endpoints are all $\le (c+g-1)a + gC'$;
and by maximality of $J$ we have $t_0 + (J+1)g > x$, i.e. $t_0 + Jg > x - g$, so the right
endpoints are all $\ge (x - g + 1)a + gV'$. So every integer $n$ of
$[\,(c+g-1)a + gC',\ (x-g+1)a + gV'\,]$ lies in the solidly covered range of its own class and is
realized. $\square$

**Lemma 3.4 (λ-lift).** ([`Sharp/Lift.lean`](../lean/Erdos1112Proof/Sharp/Lift.lean)) *Suppose the box $(Y, Z)$ mod $a$ (Lemma 3.2 with $\nu = a$,
$(g_1, g_2) = (b, M)$) covers all residues with budget $B \le M - 1$ for the triple $(a, b, M)$,
and $Y + Z \le a - 1$. Then the same box has budget $\le M' - 1$ for $(a,\ b + a,\ M + a)$.*
*Proof.* Residues of $jb + kM$ mod $a$ are unchanged, so the same representative pairs serve; each
rep height grows by $(j + k)a \le (Y + Z)a$, so $S' \le S + (Y+Z)a$ and
$\lceil (M' - 1 + S')/a \rceil \le \lceil (M - 1 + S)/a \rceil + Y + Z + 1$. The budget grows by
at most $Y + Z + 1 \le a$, the target by exactly $a$. $\square$

### III.2 Reduction to the hard core

**Lemma 3.5 (Graham reduction).** ([`Sharp/Graham.lean`](../lean/Erdos1112Proof/Sharp/Graham.lean)) *(SHARP) for all alphabets follows from (SHARP) for
**irreducible** ones: $|G| = 3$, or $|G| \ge 4$ minimal (no proper subset of size $\ge 3$ has gcd
1).* *Proof.* Graham's growth lemma (R. L. Graham, Duke Math. J. 31 (1964), 275–285): if the
subset sums contain a run of $\ell$ consecutive integers and $g \in G$ has $g \le \ell$, adjoining
one copy of $g$ extends the run to length $\ell + g$. Induct on $|G|$: if $|G| \ge 4$ is not
irreducible, some $e$ is redundant ($\gcd(G \setminus \{e\}) = 1$, $|G \setminus \{e\}| \ge 3$).
If $e \ne M$: any witness for $G \setminus \{e\}$ is one for $G$. If $e = M$: let
$M' = \max(G \setminus \{M\})$; by induction a run of length $\ge M'$ costs $\le M' - 1$; Graham
fill with copies of $a$ costs $\le \lceil (M - M')/a \rceil \le M - M'$, total $\le M - 1$.
$\square$

**Lemma 3.6 (L1: small coprime pair).** *If some coprime pair $\alpha, \gamma \in G$ has
$\alpha + \gamma \le M - 1$, then $m(G) \le M - 1$.*
*Proof.* Take $x = M - \alpha$ copies of $\alpha$ and $\alpha - 1$ copies of $\gamma$: by Lemma
3.2 (modulus $\alpha$, reps $j\gamma$) the sums cover $[(\alpha - 1)\gamma,\ x\alpha]$, of length
$x\alpha - (\alpha - 1)\gamma + 1 \ge (M-\alpha)\alpha - (\alpha - 1)(M - \alpha - 1) + 1 = M$;
budget $(M - \alpha) + (\alpha - 1) = M - 1$. $\square$

**Lemma 3.7 (L2: pair at the boundary).** *A coprime pair $\alpha < \beta$ in $G$ with
$\alpha + \beta \in \{M, M+1\}$ gives $m(G) \le M - 1$.*

*Proof.* For an integer $t \ge 0$, take $x = \beta - 1$ copies of $\alpha$ and
$y = \alpha - 1 + t$ copies of $\beta$. The hypotheses of Lemma 3.1 ($x \ge \beta - 1$,
$y \ge \alpha - 1$) hold, so the subset sums contain the interval
$[C,\ \alpha x + \beta y - C]$, $C = (\alpha - 1)(\beta - 1)$, whose length is
$\alpha x + \beta y - 2C + 1 = \alpha + \beta - 1 + t\beta$, at budget
$x + y = \alpha + \beta - 2 + t$. The two boundary values of $\alpha + \beta$ require
**different** values of $t$:

- **Case $\alpha + \beta = M + 1$: take $t = 0$.** Run length $\alpha + \beta - 1 = M$;
  budget $\alpha + \beta - 2 = M - 1$.
- **Case $\alpha + \beta = M$: take $t = 1$.** Run length
  $\alpha + \beta - 1 + \beta = M - 1 + \beta \ge M$ (since $\beta \ge 2$); budget
  $\alpha + \beta - 2 + 1 = M - 1$. Here $t = 0$ would give run length only
  $\alpha + \beta - 1 = M - 1 < M$; one further copy of $\beta$ is needed, and the budget
  $M - 1$ absorbs it exactly.

*Worked example, $(\alpha, \beta, M) = (2, 3, 5)$ (the case $\alpha + \beta = M$).* With $t = 0$
the multiset is $\{2, 2, 3\}$: subset sums $\{0, 2, 3, 4, 5, 7\}$, longest run $[2, 5]$ of
length $4 < 5$ — insufficient, exactly as the boundary bookkeeping predicts. With $t = 1$ the
multiset is $\{2, 2, 3, 3\}$, budget $4 = M - 1$: subset sums
$\{0, 2, 3, 4, 5, 6, 7, 8, 10\} \supseteq [2, 8]$, a run of $7 \ge 5$ consecutive integers.

*Verification.* Both cases were checked by exact subset-sum computation over **all** coprime
pairs $\alpha < \beta$ with $\alpha + \beta \in \{M, M+1\}$ and $M \le 200$: 6,115 pairs with
$\alpha + \beta = M$ (each at $t = 1$: budget $= M - 1$, run $\ge M - 1 + \beta \ge M$) and
6,180 pairs with $\alpha + \beta = M + 1$ (each at $t = 0$: budget $= M - 1$, run $\ge M$);
zero failures. $\square$

**Lemma 3.8 (L3: non-coprime pair).** *If $|G| = 3$ and $a, b \in G \setminus \{M\}$ have
$d := \gcd(a, b) \ge 2$ (then $\gcd(d, M) = 1$ automatically), then $m(G) \le M - 1$.*
*Proof.* Write $a = d\alpha$, $b = d\beta$. Take $x = \beta - 1$ copies of $a$,
$y = M - d - \beta + 1$ copies of $b$, $d - 1$ copies of $M$: budget exactly $M - 1$. The
$(a, b)$-grid gives (Lemma 3.1, scaled by $d$) a $d$-AP of length
$L = \alpha x + \beta y - 2(\alpha - 1)(\beta - 1) + 1$. The requirement $y \ge \alpha - 1$
follows from $M \ge d\beta + 1$ via $(d - 1)(\beta - 1) \ge \alpha - 2$; and $L \ge M + 1$: this
is monotone in $M$, and at the worst case $M = d\beta + 1$ it reduces to
$d\beta(\beta - 2) - \beta^2 - \alpha\beta + \alpha + 4\beta - 3 \ge 0$, which for $d \ge 2$
follows from $\beta(\beta - \alpha) + \alpha - 3 \ge 0$, true for all $1 \le \alpha < \beta$.
Bridging the $d$ residues by $kM$, $k \le d - 1$ ($\gcd(d, M) = 1$), covers
$[\,dC_{\alpha\beta} + (d-1)M,\ dC_{\alpha\beta} + (L-1)d\,]$, of length $\ge M$ (the requirement
$(L-1)d \ge dM - 1$ is equivalent, both sides being considered mod $d$, to $L \ge M + 1$).
$\square$

**Lemma 3.9 (structure of minimal alphabets).** *Let $G = \{g_1, \dots, g_m\}$ be minimal (no
proper subset of size $\ge 3$ has gcd 1), $m \ge 4$, and $d_i := \gcd(G \setminus \{g_i\})$. Then
each $d_i \ge 2$; the $d_i$ are pairwise coprime (for $i \ne j$, $\gcd(d_i, d_j)$ divides every
element of $(G \setminus \{g_i\}) \cup (G \setminus \{g_j\}) = G$, hence divides $\gcd(G) = 1$);
and $d_j \mid g_i$ for every $j \ne i$. Hence every $g_i$ is divisible by $\prod_{j \ne i} d_j$, a
product of $m - 1 \ge 3$ pairwise coprime integers $\ge 2$: so $g_i \ge 2 \cdot 3 \cdot 5 = 30$
for $m = 4$, and $g_i \ge 210$ for $m \ge 5$. Also every pair of elements of $G$ has gcd $\ge 2$
(a coprime pair would lie in a gcd-1 proper triple).* $\square$

*(Enumeration, machine-checked two independent ways: there are exactly 6 minimal 4-alphabets with
$M \le 110$ and 12 with $M \le 130$, the smallest being $\{30, 42, 70, 105\}$ with $M = 105$; no
minimal alphabet of any size has $M < 105$; $|G| \ge 5$ is impossible below $M = 210$.)*

**Lemma 3.10 (L4: minimal alphabets, $|G| \ge 4$).** ([`Sharp/Graham.lean`](../lean/Erdos1112Proof/Sharp/Graham.lean)) *If $G$ is minimal with $|G| \ge 4$, then
$m(G) \le M - 1$.*
*Proof.* Remove the smallest element $a$: $G' := G \setminus \{a\}$ has
$\gcd(G') =: \delta \ge 2$ (minimality), $M \in G'$, and $H := G'/\delta$ is an alphabet with
$\gcd(H) = 1$, $\max H = M/\delta < M$, $|H| \ge 3$. By strong induction on $M$ (the theorem for
smaller maxima), a run of length $\max H$ costs $\le M/\delta - 1$ within $H$; Graham-filling with
$a' := \min H$ to length $\ell := \lceil (M - 1 + (\delta - 1)a)/\delta \rceil + 1$ costs
$\le (M/\delta - 1) + \lceil (\ell - M/\delta)/a' \rceil$; scaling by $\delta$ and bridging the
$\delta$ residues with $k$ copies of $a$, $k \le \delta - 1$ ($\gcd(a, \delta) = 1$ since
$\gcd(G) = 1$), covers an interval of length $\ge M$ at total budget
$$T \le \Big(\frac M\delta - 1\Big) + \Big\lceil \frac{\ell - M/\delta}{a'} \Big\rceil +
(\delta - 1).$$
Now $a < \min G' = \delta a'$, i.e. $a \le \delta a' - 1$, whence
$\ell - M/\delta \le (\delta - 1)a/\delta + 2 < (\delta - 1)a' + 2$ and
$\lceil (\ell - M/\delta)/a' \rceil \le \delta + 1$; so $T \le M/\delta + 2\delta - 1$, and
$T \le M - 1 \iff M(1 - 1/\delta) \ge 2\delta \iff M \ge 2\delta^2/(\delta - 1)$. For
$\delta \ge 3$: $2\delta^2/(\delta - 1) \le 3\delta \le M$ ($G'$ contains $\ge 3$ distinct
multiples of $\delta$). For $\delta = 2$: it needs $M \ge 8$, guaranteed since every element is
$\ge 30$ (Lemma 3.9). The bound never divides by $a'$ except through $a \le \delta a' - 1$, so
$a' = 1$ is subsumed. $\square$
*(The construction was verified end-to-end on all 12 minimal alphabets with $M \le 130$: budgets
16–24 against $M - 1 \ge 104$.)*

**The hard core.** By Lemmas 3.5–3.10, (SHARP) reduces to: $G = \{a, b, M\}$, $\gcd(a, b) = 1$,
and (by L1/L2 applied to the pair $(a,b)$) $\delta := a + b - M \ge 2$. Notation for the rest of
Part III:
$$e := b - a \ge 1,\quad h := M - b \in [1,\ a - 2],\quad \mu := e + h = M - a,\quad
\delta = a - h,\quad \gcd(a, e) = 1,\quad a \ge 3,$$
$g := \gcd(e, h) = \gcd(e, \mu)$ (coprime to each of $a, b, M$), $\bar e := e \bmod a \in
[1, a-1]$, $\bar\mu := M \bmod a$, and — when $\bar\mu \ne 0$ —
$\eta := \bar\mu \cdot \bar e^{-1} \bmod a$. Note $\eta = 1$ is impossible ($\eta = 1 \iff a \mid
h$, but $1 \le h \le a - 2$), and
$$\eta = 0 \iff a \mid M; \qquad \eta = a - 1 \iff a \mid b + M,$$
and these two lines are disjoint ($a \mid M$ and $a \mid b + M$ would force $a \mid b$). The
target budget is $M - 1$ throughout. The proof is a decision tree; the six cases below cover the
hard core (checklist in Part IV).

**Roadmap of the six cases.** Each hard-core $(a, b, M)$ is routed to exactly one branch, evaluated
top to bottom (full dispatch in §III.9):

- **Case D** — $a \mid M$ (§III.3);
- **Case P** — else $a \mid b + M$ (the $\eta = -1$ line; §III.4);
- **Case L** — else $e = h$ (scaled consecutive triples; §III.5);
- **Case E** — else $a \ge 12$ and $\mu \ge 12$ (the universal $\eta$-box; §III.6);
- **Case T** — else $\mu \le 11$ (finitely many staircase lines; §III.7);
- **Case B** — else $a \le 11$, $\mu \ge 12$ (finite bases + $\lambda$-lift; §III.8).

The branches are mutually exclusive by construction and exhaustive (Part IV checklist); each yields a
covering multiset of size $\le M - 1$.

### III.3 Case D: $a \mid M$ (half-price padding)

**Lemma 3.11 (D).** ([`Sharp/CaseD.lean`](../lean/Erdos1112Proof/Sharp/CaseD.lean)) *If $a \mid M$, write $M = qa$ with $q \ge 2$, and put
$x_{\rm eff} := \lceil (M - 1 + (a-1)b)/a \rceil$. The multiset with $a - 1$ copies of $b$,
$q - 1$ copies of $a$, and $z := \lceil (x_{\rm eff} - (q-1))/q \rceil$ copies of $M$ has budget
$\le M - 1$, and its subset sums contain $M$ consecutive integers.*

*Proof.* *Coverage.* The $a - 1$ copies of $b$ realize $\{jb : 0 \le j \le a - 1\}$, a complete
residue system mod $a$ (as $\gcd(a, b) = 1$), with top $S = (a-1)b$. The padding realizes
$\{ia + kM : 0 \le i \le q - 1,\ 0 \le k \le z\} = a\{i + qk\} \supseteq a\,[0,\ (q-1) + qz]$ (the
blocks $[qk,\ qk + (q-1)]$ abut, each having length $q$), and $(q-1) + qz \ge x_{\rm eff}$ by the
choice of $z$. By Lemma 3.2 the subset sums cover $[S,\ S + M - 1]$, an interval of $M$
consecutive integers.

*Budget — uniform in $q$, with no sub-cases.* Since $b \le M - 1$,
$\tfrac{M - 1 + (a-1)b}{a} \le \tfrac{M - 1 + (a-1)(M-1)}{a} = M - 1$, so $x_{\rm eff} \le M - 1
= qa - 1$, whence
$$z = \Big\lceil \tfrac{x_{\rm eff} - (q-1)}{q} \Big\rceil \le \Big\lceil \tfrac{qa - 1 - (q-1)}{q}
\Big\rceil = \Big\lceil \tfrac{q(a-1)}{q} \Big\rceil = a - 1.$$
Therefore
$$(a-1) + (q-1) + z \;\le\; (a-1) + (q-1) + (a-1) \;=\; 2a + q - 3 \;\le\; qa - 1 = M - 1,$$
the last inequality being exactly $(a-1)(q-2) \ge 0$, valid for all $q \ge 2$, $a \ge 3$. Thus a
single construction closes the whole case — no $q = 2$ / $q \ge 3$ split and no separate
$b = 2a - 1$ endpoint. $\square$

### III.4 Case P: $a \mid b + M$ (the $\eta = -1$ line)

Here $b + M = ra$ for an integer $r \ge 3$, and copies of $b$ and $M$ act as opposite residue
steps mod $a$: a $(b, M)$-pair is a residue-free mover worth $r$ grid units of $a$ at cost 2.

The formalization collapsed this case. The two pair families (formerly separate lemmas for
$r = 3$ and $r = 4$) together with the three ad-hoc corner certificates are all instances of a
single **uniform pair-frame**, and the manuscript's earlier finite subset-sum check for small
$a$ was replaced by a symbolic argument. We state that construction as one $r$-parameterized
lemma.

**Lemma 3.12 (uniform pair-frame; $\eta = -1$).** ([`Sharp/CaseP.lean`](../lean/Erdos1112Proof/Sharp/CaseP.lean)) *Let $b + M = ra$ with $r \ge 3$. The
multiset consisting of $r - 1$ copies of $a$, $\lceil (M-r)/2 \rceil$ copies of $b$, and
$\lfloor (M-r)/2 \rfloor$ copies of $M$ has budget exactly*
$$(r-1) + \big\lceil \tfrac{M-r}2 \big\rceil + \big\lfloor \tfrac{M-r}2 \big\rfloor = M - 1,$$
*and its subset sums contain $M$ consecutive integers for $r \in \{3, 4\}$ and every $a \ge 3$
(and, as instances, for the three $r = 5$ corner triples below).*

*Proof.* Write $(x, y, z) = (r-1,\ \lceil (M-r)/2 \rceil,\ \lfloor (M-r)/2 \rfloor)$. Any
selection is $v = ia + jb + kM = ia + wb + rak$ with $w := j - k$ (using $M = ra - b$) and
$i \le x = r - 1$; the constraints are $k \ge \max(0, -w)$, $k \le z$, $w + k \le y$.
*Residues:* put $s := b \bmod a$, so $\gcd(s, a) = 1$; given $n$, choose
$w^* \in (-a/2,\ a/2]$ with $w^* s \equiv n \pmod a$, then $n - w^* b \equiv \gamma a
\pmod{ra}$ for some $\gamma \in \{0, 1, \dots, r-1\}$ and set $i := \gamma \le r - 1$. So every
residue mod $ra$ is $ia + w^* b$ with $i \le r - 1$, $|w^*| \le W^* := \lceil (a-1)/2 \rceil$.
*Heights and reach:* class $(i, w)$ is covered at heights $ia + wb + rak$ for
$k \in [\max(0, -w),\ \min(z,\ y - w)]$, an AP of step $ra$ with at least $\min(y, z) - |w|$
steps above its start $S(i, w) = ia + wb + ra\max(0, -w) \le (r-1)a + W^* M$. Hence all of
$[\,(r-1)a + W^* M,\ ra \min(y, z) - W^* M\,]$ is covered; its length is at least
$ra \lfloor (M-r)/2 \rfloor - 2W^* M - (r-1)a + 1 \ge M$. For $r = 3$ this reduces (with
$M \ge \tfrac32 a$, $W^* \le (a+1)/2$) to $M(a-4) \ge 16a$, i.e. $a \ge 15$, and $r = 4$ closes
analogously; the finitely many triples with smaller $a$ — including the three $r = 5$ instances
listed below — are a finite check, carried out symbolically in the formalization (the tighter
run-start accounting there reaches every $a \ge 8$, and the residual $a \le 7$ triples are
decided; see the Remark and Appendix D). $\square$

**Remark (elimination of the small-$a$ computer check; discovered in formalization).** In the
manuscript's earlier form the two pair families were proved to close only for $a \ge 15$ (the
estimate in the proof above), and *every* member with $a \le 14$ — in fact all $4{,}325$ members
with $a \le 120$ — was verified by exact subset-sum computation. The formalization instead fixes
the run start at $\max((r{-}1)b,\ (r{-}1)M)$ and lands each target via its signed representative
through four corner inequalities; this tighter accounting closes the reach for all $a \ge 8$, and
the residual $a \le 7$ triples form a finite, explicitly enumerable set decided symbolically. The
formal proof (Appendix D) therefore carries **no** subset-sum search in Case P — the same
closed-form multiset is verified for every $a \ge 3$. Moreover the three formerly
ad-hoc certificates of the $r \ge 5$, $M < 2a + 4$ corner,
$$(3,7,8):\ (x,y,z) = (4,2,1); \qquad (4,9,11):\ (4,3,3); \qquad (5,12,13):\ (4,4,4),$$
are exactly this multiset at $r = 5$ (where $x = r - 1 = 4$), no longer a separate list.

**Lemma 3.14 (ETAneg; $M \ge 2a + 4$).** ([`Sharp/CaseP.lean`](../lean/Erdos1112Proof/Sharp/CaseP.lean)) *If $a \mid b + M$ and $M \ge 2a + 4$, the hard-core
triple $(a, b, M)$ admits a multiset of budget $\le M - 1$ whose subset sums contain $M$
consecutive integers.*

*Proof.* Since $\bar\mu = a - \bar e$, the reps $jb + kM \equiv \bar e (j - k) \pmod a$ cover
$\mathbb{Z}_a$ with any box $(Y, Z)$, $Y + Z = a - 1$ ($j - k$ ranges over $[-Z, Y]$, a complete
residue system). Choose $Y = \lceil (a-1)/2 \rceil$, $Z = \lfloor (a-1)/2 \rfloor$. The minimal rep
of class $\bar e w$ has height $wb$ ($w \ge 0$) or $|w|M$ ($w < 0$), so $S \le \max(Yb,\ ZM)$, and
the budget $\lceil (M - 1 + S)/a \rceil + (a - 1) \le M - 1$ iff $S \le (a-1)M - a^2 + 1$. Both
branches of the max satisfy this for $M \ge 2a + 4$; for $a$ odd already for $M \ge 2a + 2$.
$\square$

**Remark (a vacuous corner, noted in formalization).** The manuscript previously handled an
$a$-even, $b = M - 1$ corner by a separate numeric bound. It is vacuous: $a \mid b + M$ forces
$b + M \equiv 0 \pmod a$, so for $a$ even $b + M$ is even and $b \le M - 2$ — the case
$b = M - 1$ cannot occur on this line, and the remaining $b \le M - 2$ configurations already
satisfy the inequality for $M \ge 2a + 4$.

**Exhaustion of Case P.** Every $\eta = -1$ triple is covered by Lemma 3.12 or Lemma 3.14:
$M < 2a$ forces $r = 3$; $M = 2a + t$ is $r = 4$; $r \ge 5$ forces
$M = ra - b \ge ra - (M - 1)$, i.e. $M \ge (5a+1)/2$, hence $M \ge 2a + 4$ (Lemma 3.14) unless
$(5a+1)/2 \le 2a + 3$, i.e. $a \le 5$. The hard-core triples with $r \ge 5$ and $M < 2a + 4$ are
exactly the three $r = 5$ instances of Lemma 3.12 recorded above. $M = 2a$ is impossible on this
line (it would imply $a \mid b$). $\square$

### III.5 Case L: $e = h = g$ (scaled consecutive triples)

**Lemma 3.15 (L).** ([`Sharp/CaseL.lean`](../lean/Erdos1112Proof/Sharp/CaseL.lean)) *For $G = \{a,\ a + g,\ a + 2g\}$, $\gcd(a, g) = 1$, $g \le a - 2$: the
multiset $(x, y, z) = (\lfloor (a-2)/2 \rfloor + 2g,\ 1,\ \lceil (a-2)/2 \rceil)$, of budget
$a + 2g - 1 = M - 1$, covers $M$ consecutive integers.*

*Proof.* Here $\mu = 2g$, $(e', \mu') = (1, 2)$, $C' = 0$, $V' = 2z + 1$, $c = z + 1$. Offsets:
$je + k\mu = g(j + 2k)$, and with $y = 1$: $\{j + 2k : j \le 1,\ k \le z\} = [0,\ 2z + 1]$,
contiguous. Note $x - c = 2g - 2$ for $a$ odd and $2g - 1$ for $a$ even. Three sub-cases:

- **$a$ even (any $g$):** here $x - c = 2g - 1 \ge g$, so $x \ge c + g$; and with $C' = 0$,
  $V' = 2z + 1$, the frame-merge condition of Lemma 3.3(d) reads $V' - C' = 2z + 1 \ge a - 1$,
  i.e. $z \ge (a-2)/2$ — exactly our $z = (a-2)/2$ (equality). Both hypotheses of the extended
  form of Lemma 3.3(d) hold, so the sums cover the solid interval
  $[\,(c + g - 1)a,\ (x - g + 1)a + g(2z+1)\,]$, of length $a + g(a - 1) + 1 \ge
  M = a + 2g \iff g(a-1) \ge 2g - 1$, true for $a \ge 3$.
- **$a$ odd, $g \ge 2$:** $z = (a-1)/2$, $x = c + 2(g-1) \ge c + g$ (as $g \ge 2$), and the
  frame-merge condition holds with room to spare: $V' - C' = 2z + 1 = a \ge a - 1$. The extended
  form of Lemma 3.3(d) gives the solid interval $[\,(c+g-1)a,\ (x-g+1)a + g(2z+1)\,]$, of length
  $g(2z+1) + 1 = ga + 1 \ge a + 2g \iff (g-1)a \ge 2g - 1$, true for $g \ge 2$, $a \ge 3$.
- **$a$ odd, $g = 1$:** here $x = c$, so Lemma 3.3(c) applies: level $c$ covers $ca + [0, V]$
  with $V = 2z + 1 = a$; level $c + 1$ covers $(c+1)a + [1, V]$; the merge condition
  $V \ge a + \max(C, 1) - 1 = a$ holds with equality, and the run $[ca,\ (c+1)a + V]$ has length
  $2a + 1 \ge a + 2 = M$. Budget $2c = a + 1 = M - 1$. $\square$

### III.6 Case E: $a \ge 12$ and $\mu \ge 12$ (the universal η-box)

**Lemma 3.16 (η-box).** ([`Sharp/CaseE.lean`](../lean/Erdos1112Proof/Sharp/CaseE.lean)) *Suppose $a \nmid M$, $a \nmid b + M$ (so $\eta \notin \{0, 1, a-1\}$),
$a \ge 12$ and $\mu = M - a \ge 12$. Let $t := \min(\eta,\ a - \eta) \in [2,\ a/2]$,
$Z := \lceil (a - t)/t \rceil$, $\sigma := t + Z$. Then the box $(Y, Z) = (t - 1,\ Z)$ covers
$\mathbb{Z}_a$ and its budget is $\le M - 1$.*

*Proof.* **Coverage:** if $t = \eta$, the box offsets are $\bar e(j + tk) \bmod a$ and
$\{j + tk : j \le t - 1,\ k \le Z\} = [0,\ t(Z+1) - 1] \supseteq [0, a-1]$ since
$t(Z + 1) \ge a$; if $t = a - \eta$, the offsets are $\bar e(j - tk)$ and $\{j - tk\} =
[-tZ,\ t-1]$, an interval of length $t(Z+1) \ge a$ — either way a complete residue system
(multiplication by the unit $\bar e$). **Budget:** with the corner bound $S \le (t-1)b + ZM$ and
$b \le M - 1$,
$$B \le \Big\lceil \frac{M - 1 + (t-1)b + ZM}{a} \Big\rceil + (t - 1) + Z \le M - 1
\iff M - 1 + S \le a(M - 1 - K),\ \ K = t - 1 + Z,$$
and the right side reduces to $M\sigma + a\sigma \le aM + t$, implied by
$M(a - \sigma) \ge a\sigma$. **Threshold:** $\sigma \le t + (a-1)/t$, whose maximum over
$t \in [2, a/2]$ is at an endpoint (convexity): $\sigma \le \max\big(\tfrac{a+3}2,\ \tfrac a2 +
2\big) = \tfrac a2 + 2$; hence
$$\frac{a\sigma}{a - \sigma} \le \frac{a(a+4)}{a - 4} = a + 8 + \frac{32}{a-4} \le a + 12
\qquad (a \ge 12),$$
so $M = a + \mu \ge a + 12$ suffices. $\square$

### III.7 Case T: $\mu \le 11$ (finitely many staircase lines)

([`Sharp/CaseT.lean`](../lean/Erdos1112Proof/Sharp/CaseT.lean)) Fix $(e, h)$ with $\mu = e + h \le 11$, $e \ne h$ (Case L), $a \nmid M$, $a \nmid b + M$. Since
$e \le 10$ and $h \le 10$, this case consists of finitely many *lines*, each parameterized by $a$
alone. Since $e \ne h$ and $e' < \mu'$, here $\mu' = \mu/g \ge 3$.

**Lemma 3.17 (T).** ([`Sharp/CaseTCore.lean`](../lean/Erdos1112Proof/Sharp/CaseTCore.lean)) *With $y = \mu' - 1$ and*
- *$g = 1$, variant A: $z = \max(e - 1,\ \lceil (\max(a, \mu) - 1 + 2C - ye)/\mu \rceil)$,
  $x = c + 1$ (Lemma 3.3(b): merge $V - C \ge a - 1$ and run length $a + V - C + 1 \ge M$);*
- *$g = 1$, variant B: $z$ from $V \ge a + \max(C, 1) - 1$ and $V \ge \mu + C - 1$, $x = c$
  (Lemma 3.3(c));*
- *$g \ge 2$: $z = \max(e' - 1,\ \lceil (a + \lceil (\mu - 1)/g \rceil + 2C' - ye')/\mu'
  \rceil)$, $x = c + g$ (Lemma 3.3(d), base form — one frame per class, no merge hypothesis
  needed: solid run length $g(V' - C') - (g-1)a + 1 \ge M$);*

*the construction covers $M$ consecutive integers whenever the stated $z$-conditions hold, at
budget $2c + v$, $v \in \{0, 1, g\}$.* Only the budget inequality $2c + v \le M - 1$ can fail,
and only finitely often:

**Lemma 3.18 (T-tail).** ([`Sharp/CaseTScan.lean`](../lean/Erdos1112Proof/Sharp/CaseTScan.lean); decided-row files [`Sharp/CaseTScanE1.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE1.lean), [`Sharp/CaseTScanE2.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE2.lean), [`Sharp/CaseTScanE3.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE3.lean), [`Sharp/CaseTScanE4.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE4.lean), [`Sharp/CaseTScanE5.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE5.lean), [`Sharp/CaseTScanE6.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE6.lean), [`Sharp/CaseTScanE7.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE7.lean), [`Sharp/CaseTScanE8.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE8.lean), [`Sharp/CaseTScanE9.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE9.lean), [`Sharp/CaseTScanE10.lean`](../lean/Erdos1112Proof/Sharp/CaseTScanE10.lean)) *(i) For every line and every $a \le 3000$, the minimal variant budget
was computed exactly: it exceeds $M - 1$ for precisely **158** triples, all with $a \le 29$ —
Table A of Appendix B — and each of those has a verified mod-$a$ box certificate with
$Y + Z \le a - 1$ and budget $\le M - 1$. (ii) For each line, the cheapest variant's budget is
bounded by the linear function*
$$\beta(a) := 2\Big[(\mu' - 1) + \frac{a + \mu + 2C' - (\mu' - 1)e'}{\mu'} + 1\Big] + g,$$
*of slope $2/\mu' \le 2/3$ in $a$ (using $\lceil u \rceil \le u + 1$ and $\mu' \ge 3$), while the
target $\tau(a) = a + \mu - 1$ has slope 1. The margin $\tau - \beta$ is nondecreasing at rate
$\ge 1/3$; at $a = 3000$ the computed minimum margin $\tau - B_{\rm exact}$ over all lines is
999 (independent implementation: 995), and since $\beta$ exceeds the exact budget by at most 2,
$\tau(3000) - \beta(3000) \ge 997 > 0$ on every line. Hence there are no failures with
$a > 3000$, and the failure set is exactly Table A.* $\square$

**Remark (a merge-lemma-free variant, from formalization).** The count "$158$" in (i) depends on
variant B, which uses the short-merge form Lemma 3.3(c). The formalization instead runs only the
two merge-robust variants (variant A and the base form), which is deliberately independent of
Lemma 3.3(c). Restricted to those, the scan reports $158 + 14 = 172$ budget failures; the extra
$14$ triples (all $a \le 29$) each carry a verified mod-$a$ box certificate of the same form as
Table A. So the paper may, if desired, drop variant B from Lemma 3.17 and enlarge Table A from
$158$ to $172$ rows, removing Case T's dependence on Lemma 3.3(c) altogether (Appendix D); at
minimum the "$158$" should be read as variant-B-dependent.

### III.8 Case B: $a \le 11$ and $\mu \ge 12$ (finite bases + λ-lift)

([`Sharp/CaseB.lean`](../lean/Erdos1112Proof/Sharp/CaseB.lean)) For $a \le 11$, the classes $(a, \bar e, h)$ with $\bar e \in [1, a-1]$, $h \in [1, a-2]$ are
finite in number, and the members of a class differ only in $\lambda = \lfloor e/a \rfloor$. For
every class reaching this case, the member of smallest $M$ was certified by an explicit mod-$a$
box with $Y + Z \le a - 1$ and budget $\le M - 1$ — Table B of Appendix B, **178** unique classes
([`Sharp/CaseBClasses.lean`](../lean/Erdos1112Proof/Sharp/CaseBClasses.lean), [`Sharp/Tables.lean`](../lean/Erdos1112Proof/Sharp/Tables.lean), [`Sharp/TablesData.lean`](../lean/Erdos1112Proof/Sharp/TablesData.lean))
— and by Lemma 3.4 (λ-lift) the same box certifies every larger member of the class. (Which
branch a triple belongs to is class-invariant for D and P — $M \bmod a$ and $(b+M) \bmod a$
depend only on $(\bar e, h)$ — while an $e = h$ member can only be the $\lambda = 0$ member;
Table B lists bases accordingly, taking the first branch-B member of each class.) $\square$

**Remark (the descent, made explicit in formalization).** The claim "every larger member of the
class is certified by the same box" is a descent that the manuscript states in prose; the
formalization renders it as a decidable argument. A triple's class is $(a,\ b \bmod a,\ h)$, and
every branch condition ($M \bmod a$, $(b+M) \bmod a$, the comparisons defining $e = h$, and the
box's residue coverage) is invariant under the descent $b \mapsto b - a$ (this is where
$\gcd(a, b - a) = \gcd(a, b)$ and the mod-$a$ recomputations enter); iterating lands on the
listed base $b_0 \le b$ with $b \equiv b_0 \pmod a$, and Lemma 3.4 (λ-lift) transports the box
upward. Concretely the enumeration for $a \le 11$ has $178$ distinct classes, of which exactly
**six** — the diagonal $\bar e = h$ classes $(9,25,32)$, $(10,27,34)$, $(11,28,34)$,
$(11,29,36)$, $(11,30,38)$, $(11,31,40)$ — must be based at a $\lambda \ge 1$ member because
their $\lambda = 0$ member has $e = h$ and belongs to Case L; these are the "first branch-B
member" re-basings named above.

### III.9 Proof of Theorem 3

([`Sharp/Main.lean`](../lean/Erdos1112Proof/Sharp/Main.lean)) By Lemmas 3.5–3.10, it suffices to treat the hard core. Given a hard-core $(a, b, M)$:
if $a \mid M$, Lemma 3.11; else if $a \mid b + M$, the uniform pair-frame (Lemma 3.12) for
$M < 2a + 4$ and Lemma 3.14 for $M \ge 2a + 4$; else if $e = h$, Lemma 3.15; else if $a \ge 12$
and $\mu \ge 12$, Lemma 3.16; else
if $\mu \le 11$, Lemmas 3.17/3.18 + Table A; else ($a \le 11$, $\mu \ge 12$) Table B + Lemma 3.4.
These cases exhaust all possibilities, and each delivers a multiset of size $\le M - 1$ whose
subset sums contain $M$ consecutive integers. $\blacksquare$

---



---
◀ [Part II — Non-existence](02-nonexistence.md) · **Next ▶** [Part IV — Assembly](04-assembly.md)
**Formalized in:** [`lean/Erdos1112Proof/Sharp/`](../lean/Erdos1112Proof/Sharp) (the D/P/L/E/T/B case files). **Finite layer independently checked by** the two Python harnesses embedded in [Appendix C](appendix-C-scripts.md).
