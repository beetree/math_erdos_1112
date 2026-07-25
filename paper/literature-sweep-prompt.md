# Prompt: targeted literature sweep for the bounded subset-sum covering lemma

Give this to a domain expert or a research assistant with library access. Attach the
paper. The goal is **not** a general survey — it is to find a specific thing, or to
establish with more confidence than we currently have that it does not exist.

---

## The prompt

I have a lemma I believe is new, and I want you to try to prove me wrong. I care much
more about a hit than about a clean bill of health, so please spend your effort trying
to find the result rather than confirming its absence.

**The statement.** For every finite set $G \subset \mathbb{Z}_{\ge 1}$ with
$|G| \ge 3$, $\gcd(G) = 1$, and $\max(G) = M$, there is a **multiset** $S$ drawn from
$G$ (repetition allowed) with $|S| \le M - 1$ whose **subset sums** — that is, sums
over sub-multisets, so 0/1 coefficients on the chosen elements — contain $M$
consecutive integers.

Write $m(G)$ for the least such $|S|$. The claim is $m(G) \le \max(G) - 1$ for every
such $G$. It is sharp: $m(\{3,4,5\}) = 4$.

**The four features that together make it unusual**, and which any candidate
antecedent must match:

1. **0/1 coefficients on a multiset** — not the $h$-fold sumset $hG$, and not
   unbounded nonnegative combinations. In coefficient space, subset sums of a bounded
   multiset form a *box* $\{0 \le c_i \le n_i\}$; $hG$ is a *simplex*
   $\{\sum c_i = h\}$. A theorem about the simplex is a weaker statement about a
   larger set and does not imply this.
2. **A uniform size bound**, $|S| \le M - 1$, depending only on $\max(G)$ — not on
   $|G|$, not on the ambient interval, not asymptotic.
3. **Consecutive integers**, difference exactly 1 — not an arithmetic progression of
   common difference $d > 1$.
4. **No density hypothesis**, and valid down to $|G| = 3$. Every result I know in this
   area needs $|A| \gtrsim \sqrt{n}$ or $|A| \gtrsim \tfrac23 \max(A)$, which is
   vacuous at three elements.

A result that gets 1–3 of these but not all four is *not* a hit, though it is worth
telling me about if it is closer than what I list below.

### Where I most want you to look

Two bodies of work were flagged to me as the likeliest homes, and I have not searched
either properly.

**(a) Numerical semigroups — Apéry sets, factorization lengths, denumerants.** This is
my top priority. The suggestion I was given was, roughly: *"if this has been proved
before, my bet is that it is there, in different language."* Specifically:

- Apéry sets $\mathrm{Ap}(S, n)$ and their combinatorial structure — is there a
  statement bounding how many generators (with repetition) are needed to realise a
  full residue system, or a run of consecutive elements?
- The **set of factorization lengths** $\mathcal{L}(x)$ of an element, and results on
  when it is an interval. My lemma is close to "some element has a factorization
  structure covering a run", so length-set literature (Chapman, García-Sánchez,
  Geroldinger, Halter-Koch, O'Neill) is plausible.
- **Denumerant** / Sylvester–Frobenius refinements that bound the *number of summands*
  rather than the Frobenius number itself. The Frobenius number is $\gg M$ and
  unbounded-multiplicity, so classical Frobenius does not apply — but a
  bounded-multiplicity refinement would.
- Delta sets, catenary and tame degrees — any invariant bounded by $\max(G) - 1$.

Translation note if you search this literature: my $G$ is a generating set, my $M$ is
the largest generator, and I need a *bounded-multiplicity* representation, which is
the unusual constraint. Most semigroup results allow unbounded multiplicity.

**(b) Algorithmic dense subset-sum.** The constructive/algorithmic line often proves
structural lemmas as a means to an end, and they get buried in the analysis rather
than stated as theorems. Please check the *proofs*, not just the theorem statements,
in:

- Bringmann and Wellnitz, on subset sums with dense inputs
- Chaimovich; Chaimovich, Freiman and Galil
- Galil and Margalit
- Koiliaris and Xu
- Chen, Mao and Zhang, arXiv:2503.19299 (constructive proofs and efficient witnesses)

In particular: any "filling lemma" or "interval-covering lemma" used internally to
show a dynamic program reaches a contiguous range.

### What I have already searched

MathSciNet, zbMATH, arXiv and Google Scholar citation chains, July 2026, around: Lev
(1997, 1998, 1999, 2003, 2022), Sárközy (finite addition theorems I/II),
Szemerédi–Vu (2006), Conlon–Fox–Pham (2021), Alon (1987), Alon–Freiman (1988),
Nathanson (1972), Granville–Walker (2021), Graham (1964), Erdős–Graham (1980),
Ramírez Alfonsín (2005). The closest antecedent I found is Lev, *On consecutive subset
sums*, Discrete Math. 187 (1998), Thm. 1 — same conclusion type (a genuine interval
from genuine 0/1 subset sums) but a dense-set theorem, $|A| \gtrsim \tfrac23 M$, and no
multiset. Section 1.9 of the attached paper has the full comparison table with a
column stating exactly which hypothesis separates each known result from mine; the
underlying search record is `paper/novelty-search.md`.

Please do not re-tread that ground unless you think I misread one of those results —
in which case say so directly, and say which row of the table is wrong.

### What I want back

1. **Any hit**, with a precise citation and the statement number, plus a sentence on
   whether it implies my lemma outright, implies it with a worse constant, or merely
   overlaps. A worse constant still counts as a hit and would change how I write the
   paper.
2. **Near misses ranked**, with the specific hypothesis that separates each from my
   statement — the same format as my table, so I can merge yours into it.
3. **Terminology I should be searching under** that I evidently am not. If this result
   exists in the numerical-semigroup literature it will not be called "subset sums",
   and knowing the right phrase is worth as much to me as a citation.
4. **A judgement**, stated plainly: is this plausibly new, or does it smell like
   folklore that someone has surely written down? I would rather hear "this feels like
   an exercise in a book I can't place" than a hedge.

If you conclude it does appear to be new, please say what you searched, so I can cite
the search honestly rather than overstate it.
