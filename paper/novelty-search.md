> **Search record.** This documents the novelty search for Theorem B; it is a search record, not a
> proof of novelty. The authoritative discussion is in the paper (`paper/erdos1112.tex`, §1.4).

# Novelty search for the bounded subset-sum interval theorem (Theorem B)

*Documented literature search supporting the novelty discussion in the paper (§1.4 /
`sec:novelty`). Conducted July 2026 over MathSciNet, zbMATH, arXiv, and Google Scholar citation
chains around the works listed below. Search terms combined "subset sums" with
"interval"/"consecutive integers", and included "finite addition theorem", "complete sequence",
"Frobenius"/"postage-stamp", "restricted additive basis", and "bounded-coefficient"/"bounded-stock
representation". This is a search record, not a proof of novelty; a domain specialist should still
confirm.*

## The statement being searched

> **(Theorem B.)** For every finite set $G \subset \mathbb{Z}_{\ge 1}$ with $|G| \ge 3$,
> $\gcd(G) = 1$ and $\max(G) = M$, there is a multiset $S$ drawn from $G$ (elements with repetition
> allowed) with $|S| \le M-1$ whose **subset sums** (0/1 coefficients on the chosen multiset)
> contain $M$ consecutive integers.

Two features distinguish it from most of the literature: (i) the object is **subset sums** (0/1
coefficients), not the $h$-fold sumset $hG$; and (ii) the size bound $|S| \le M-1$ is **uniform** —
it depends only on $M = \max(G)$ and holds for every $G$ down to $|G| = 3$.

## Verdict

**Appears to be new.** No searched source proves it or immediately implies it, even with a worse
constant. It is best described as a *bounded-support, uniform-size* sharpening of the subset-sum
interval phenomenon.

## Closest known results, and why each falls short

| Result | What it gives | Why it does not imply Theorem B |
|---|---|---|
| **Lev**, finite addition theorem I (*J. Number Theory* **62** (1997), Thm. 1) | an interval of length exactly $\max(A)+1$ | inside the $h$-fold sumset $(2k-1)A$ (unbounded multiplicities, many summands), under a density hypothesis — not 0/1 subset sums of a bounded multiset |
| **Lev / Sárközy**, subset-sum addition theorem (finite addition thm II) | an AP in the 0/1 subset sums $S(A)$ | common difference $d \le 4m/n$ **cannot be forced to 1** (no consecutive integers); needs a large set $n \sim \sqrt{m\log m}$; vacuous at $|G|=3$ |
| **Szemerédi–Vu**, *Ann. of Math.* **163** (2006) | subset sums of $A\subseteq[n]$ contain a length-$n$ AP | density threshold $\lvert A\rvert \ge c\sqrt n$; an AP, not necessarily consecutive integers; no uniform $\lvert S\rvert\le M-1$ bound |
| **Conlon–Fox–Pham**, arXiv:2104.14766 (2021) | long interval of consecutive integers in subset sums (homogeneous strengthening of Szemerédi–Vu) | asymptotic / density-based; yields no uniform small $\lvert S\rvert \le M-1$ |
| **Nathanson** (1972, threshold $m\ge(\max A)^2(n-1)$); **Granville–Walker**, *PAMS* **149** (2021), Thm. 1.1; **Lev**, *PAMS* **150** (2022), Thm. 3 | interval structure of $mA$ for large $m$ (whole interval minus fixed end-caps) | the $h$-fold sumset is a *simplex* $\{\sum c_i=m\}$ in coefficient space; subset sums of a bounded multiset are a *box* $\{0\le c_i\le n_i\}$ **contained** in it, so "$mA$ ⊇ interval" is a weaker statement about a larger set; even where the $|G|=3$ threshold $\max-1$ matches our budget $M-1$, the shapes differ (per-generator vs total cap) |
| **Alon–Freiman**, *Combinatorica* **8** (1988); **Sárközy** I/II | AP / interval in subset sums of a **dense** set | density $\lvert A\rvert\gtrsim\sqrt n$; vacuous at $\lvert G\rvert=3$ |
| **Alon**, *J. Number Theory* **27** (1987) | extremal size of a **set** avoiding a target subset sum | the inverse (avoidance) problem; orthogonal |
| **Completeness**: Folkman, Birch, Graham (*Duke* **31** (1964)), Erdős–Graham | subset sums of an **infinite** sequence contain all large integers | infinite sequence, unbounded summands; the "filling" step is a shared *technique*, not an implication |
| **Frobenius / numerical semigroups**, Ramírez Alfonsín (2005) | all integers past the Frobenius number, as **unbounded** nonnegative combinations | Frobenius number $\gg M$; unbounded multiplicity; no length-$M$ window from a bounded multiset |
| **Postage-stamp / restricted additive bases** | initial run $[1,N]$ using $\le h$ summands | the generating set is *chosen* to maximize $N$; Theorem B fixes an *arbitrary* $G$ and a run of length exactly $M$ |

## The single structural reason none applies

The literature splits into two regimes, and Theorem B sits between them: the *higher-sumset* results
($mA$, many summands, unbounded multiplicities) and the *density-threshold subset-sum* results
(large $|A|$, APs of common difference possibly $>1$). Theorem B instead demands a **bounded** number
of summands (size $\le M-1$) drawn with repetition from a **fixed, possibly tiny** generating set,
whose 0/1 subset sums cover an interval of length **exactly** $\max(G)$, uniformly in $G$. No
searched theorem controls all of: bounded multiset size, 0/1 (not $h$-fold) coefficients, consecutive
integers (not an AP with $d>1$), and uniformity in $G$ down to $|G|=3$.

## Caveats

Novelty in a mature area cannot be settled negatively by search alone. This search, though broad,
was not exhaustive; the sharpest place for a specialist to look is the immediate neighbourhood of
Lev's finite addition theorems, with which Theorem B shares the "interval of length $\max$" feature.

## Primary sources consulted

- V. F. Lev, *Optimal representations by sumsets and subset sums*, J. Number Theory **62** (1997), 127–143.
- V. F. Lev, *The structure of multisets with a small number of subset sums*, Astérisque **258** (1999).
- V. F. Lev, *The structure of higher sumsets*, Proc. Amer. Math. Soc. **150** (2022); arXiv:2110.03554.
- E. Szemerédi, V. H. Vu, *Finite and infinite arithmetic progressions in sumsets*, Ann. of Math. (2) **163** (2006), 1–35.
- D. Conlon, J. Fox, H. T. Pham, *Subset sums, completeness and colorings*, arXiv:2104.14766 (2021).
- A. Granville, A. Walker, *A tight structure theorem for sumsets*, Proc. Amer. Math. Soc. **149** (2021).
- M. B. Nathanson, *Sums of finite sets of integers*, Amer. Math. Monthly **79** (1972), 1010–1012.
- N. Alon, *Subset sums*, J. Number Theory **27** (1987), 196–205.
- N. Alon, G. Freiman, *On sums of subsets of a set of integers*, Combinatorica **8** (1988), 297–306.
- A. Sárközy, *Finite addition theorems, I / II*, J. Number Theory **32** (1989), 114–130; **48** (1994), 197–218.
- V. F. Lev, *Blocks and progressions in subset sum sets*, Acta Arith. **106** (2003).
- R. L. Graham, *Complete sequences of polynomial values*, Duke Math. J. **31** (1964), 275–285.
- P. Erdős, R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monogr. Enseign. Math. **28**, 1980.
- J. L. Ramírez Alfonsín, *The Diophantine Frobenius Problem*, Oxford Univ. Press, 2005.
- Chen–Mao–Zhang, *Long arithmetic progressions in sumsets and subset sums: constructive proofs and efficient witnesses*, arXiv:2503.19299 (2025) — used to confirm the verbatim statements of the Lev/Sárközy addition theorems.
