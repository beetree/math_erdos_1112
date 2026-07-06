*Erdős #1112 · [Index](../README.md) · Part I of IV*

## Part I. Existence for $d_2 \ge k+1$

**Theorem 1.** Let $k \ge 2$, $d_2 \ge k+1$, $1 \le d_1 < d_2$. Then $r_k(d_1,d_2) \le 192\,d_2$.
*(The Lean formalization covers $k \ge 3$, the range of the Main Theorem; the $k = 2$ case is
established here in prose only — this is the one place "formally verified" reaches less far than the
prose.)*

*Proof.* Fix $B$ with $b_{i+1} \ge r b_i$, $r := 192\,d_2$. We construct $A$ inside a Beatty
family.

**(1.1) Beatty cluster containment.** ([`Existence/Beatty.lean`](../lean/Erdos1112Proof/Existence/Beatty.lean)) For real $\gamma \in (d_2 - 1, d_2)$ and an integer
$c \ge 0$ let $A_{\gamma,c} := \{c + \lfloor i\gamma \rfloor : i \ge 1\}$. Its gaps lie in
$\{d_2 - 1, d_2\} \subseteq [d_1, d_2]$. For any $i_1, \dots, i_k \ge 1$ with $s := \sum_t i_t$,
$$\sum_t \lfloor i_t \gamma \rfloor \in (s\gamma - k,\ s\gamma],$$
since $i_t\gamma - 1 < \lfloor i_t\gamma \rfloor \le i_t\gamma$. Hence
$$kA_{\gamma,c} \subseteq \bigcup_{s \ge k} \big( kc + s\gamma - k,\ kc + s\gamma \big].$$
Consequently, if for a given $b$ no integer $s \ge 1$ satisfies
$s\gamma \in [\,b - kc,\ b - kc + k\,]$ (a closed, hence safer, criterion), then
$b \notin kA_{\gamma,c}$. No irrationality of $\gamma$ is needed.

**(1.2) Free-gap lemma.** ([`Existence/FreeGap.lean`](../lean/Erdos1112Proof/Existence/FreeGap.lean)) *Let $t \ge 32 d_2^2$ and let $I \subseteq [d_2 - 1/2,\ d_2]$ be a
closed interval with $|I| \ge 4d_2^2/t$. Then $I$ contains a closed subinterval $I'$ with
$|I'| \ge d_2/(48t)$ such that every $\gamma \in I'$ satisfies $s\gamma \notin [t, t+k]$ for all
integers $s \ge 1$.*

*Proof.* Write $I = [lo, hi]$, so $d_2 - 1/2 \le lo \le hi \le d_2$ and $hi - lo \ge 4d_2^2/t$.
A $\gamma$ satisfies $s\gamma \notin [t, t+k]$ for all $s \ge 1$ iff $\gamma$ avoids the "unsafe"
set $U := \bigcup_{s \ge 1} [\,t/s,\ (t+k)/s\,]$. Rather than count all unsafe intervals meeting
$I$, we *name a single gap*. Put
$$s_1 := \lceil t/hi \rceil \quad(\text{the least } s \text{ with } t/s \le hi), \qquad
   R := t/s_1, \qquad L := (t+k)/(s_1+1),$$
and let $J := (L, R)$ be the gap between the $s_1$-th and $(s_1{+}1)$-st unsafe intervals. From
$t/hi \le s_1 < t/hi + 1$ and $hi \in [d_2 - 1/2,\ d_2]$, $t \ge 32 d_2^2$ one has
$$\tfrac{t}{d_2} \le s_1,\qquad s_1 \ge 32 d_2,\qquad s_1 + 1 \le \tfrac{5t}{d_2}. \tag{1.2.1}$$

*(i) $J$ avoids $U$.* If $s \le s_1$ then $t/s \ge t/s_1 = R$, so any $\gamma < R$ has
$s\gamma < t$; if $s \ge s_1 + 1$ then $(t+k)/s \le (t+k)/(s_1+1) = L$, so any $\gamma > L$ has
$s\gamma > t+k$. Hence a single $\gamma \in J$ misses **every** interval $[t/s, (t+k)/s]$ at once
— no relevant-range enumeration is needed.

*(ii) $|J| \ge d_2/(16t)$.* We have $R - L = (t - k\,s_1)/(s_1(s_1+1))$. Since $s_1 \le t/hi + 1
\le t/(d_2 - 1/2) + 1$ and $k \le d_2 - 1$,
$$\begin{aligned}
\big(k + \tfrac{15}{32}\big)s_1
  &\le \big(d_2 - \tfrac{17}{32}\big)\Big(\tfrac{t}{d_2 - 1/2} + 1\Big) \\
  &= t - \tfrac{t}{32(d_2 - 1/2)} + \big(d_2 - \tfrac{17}{32}\big) \\
  &\le t,
\end{aligned}$$
the last step because $t \ge 32 d_2^2$ gives $t/(32(d_2 - 1/2)) = d_2^2/(d_2 - 1/2) \ge
d_2 + \tfrac12 > d_2 - \tfrac{17}{32}$. Thus $t - k\,s_1 \ge \tfrac{15}{32}s_1$, and with
$(1.2.1)$,
$$R - L \ge \frac{15}{32}\cdot\frac{1}{s_1 + 1} \ge \frac{15}{32}\cdot\frac{d_2}{5t}
   = \frac{3}{32}\cdot\frac{d_2}{t} \ge \frac{d_2}{16t}.$$

*(iii) $J \subseteq I$.* $R = t/s_1 \le hi$ by the choice of $s_1$, and $s_1 < t/hi + 1$ gives
$R > t/(t/hi + 1) > hi - hi^2/t \ge hi - d_2^2/t$. Also $R - L \le t/(s_1(s_1 + 1)) \le
t/(t/hi)^2 \le d_2^2/t$, so $L = R - (R-L) \ge (hi - d_2^2/t) - d_2^2/t = hi - 2d_2^2/t \ge
hi - \tfrac12(hi - lo) \ge lo$. Hence $[L, R] \subseteq [lo, hi] = I$.

Take $I'$ to be the closed middle third of $J$: then $I' \subseteq I$, every $\gamma \in I'$
avoids $U$ by (i), and $|I'| = |J|/3 \ge d_2/(48t)$ by (ii). $\square$

This single-index argument is the one carried out in the formalization
(`exists_safe_subinterval`, Appendix D); it replaces the earlier endpoint-spacing count and is
what makes the containment $J \subseteq I$ explicit rather than asserted.

**(1.3) Small elements of $B$.** $B$ is infinite, so some $b_{j_0} \ge 4d_2^2$ exists with all
smaller elements of $B$ below it. Set $c := b_{j_0} + 1$. Then
$\min kA_{\gamma,c} \ge k(c + d_2 - 1) > kc > b_{j_0}$, so every $b_i \le b_{j_0}$ is below
$\min kA$ and automatically avoided. For $i > j_0$ put $t_i := b_i - kc > 0$. Since
$(x - \tau)/(y - \tau) \ge x/y$ for $x \ge y > \tau \ge 0$, the shifted targets keep ratio:
$t_{i+1}/t_i \ge b_{i+1}/b_i \ge 192 d_2$. Also
$t_{j_0+1} = b_{j_0+1} - kc \ge 192 d_2 b_{j_0} - d_2(b_{j_0} + 1) \ge 96\,d_2 b_{j_0}
\ge 384\,d_2^3 \ge 32 d_2^2$.

**(1.4) Nested intervals.** ([`Existence/Nested.lean`](../lean/Erdos1112Proof/Existence/Nested.lean)) Start with $I_0 := [d_2 - 1/2,\ d_2 - 1/4]$
($|I_0| = 1/4 \ge 4d_2^2/t_{j_0+1}$ by (1.3)). Inductively, given $I_j$ safe for
$t_{j_0+1}, \dots, t_{j_0+j}$ with $|I_j| \ge d_2/(48\, t_{j_0+j})$, apply (1.2) with
$t = t_{j_0+j+1}$: the hypothesis $|I_j| \ge 4d_2^2/t$ reduces to
$t_{j_0+j+1} \ge 192\, d_2\, t_{j_0+j}$, which is exactly what $r = 192 d_2$ supplies. The
intersection $\bigcap_j I_j$ of nested closed intervals contains a point $\gamma^*$, safe for
every $t_i$ simultaneously. By (1.1), $(kA_{\gamma^*,c}) \cap B = \emptyset$. $\square$

*Verification note.* Beyond the proof, the construction was executed exactly (rational-interval
arithmetic) against sample lacunary $B$ (ratios 16 and 40, $d_2 = 4$, $k = 3$, targets to
$10^{14}$; and $k = 5$, $d_2 = 6$ at $r = 30$ and $r = 1152$, with the (1.3) offset), and the
resulting $\gamma$ checked both by brute-force computation of $kA$ and by criterion (1.1): zero
violations.

---



---
◀ [Overview](00-overview.md) · **Next ▶** [Part II — Non-existence](02-nonexistence.md)
**Formalized in:** [`lean/Erdos1112Proof/Existence/`](../lean/Erdos1112Proof/Existence) (`Beatty.lean`, `FreeGap.lean`, `Nested.lean`).
