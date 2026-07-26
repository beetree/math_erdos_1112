# Final review prompt — falsification pass

Attach `paper/erdos1112.pdf`. Run with several reviewers independently. This prompt
is deliberately narrower than the previous rounds: the goal is to *close*, not to
improve further.

---

## The prompt

This paper has been through five rounds of adversarial review. Each round improved
it, and each round also introduced new defects in the repairs themselves — last
round, three of five findings were in text added by the two commits before it, and
none was on the critical path. Fresh prose is unverified prose. I am trying to
close, not to keep polishing.

**I am therefore asking you for one thing: tell me if anything in this paper is
false.** Not what could be added, clarified, expanded, restructured, or better
motivated. Only what is *wrong*.

Please do not suggest new sections, new remarks, new open problems, new examples,
new appendices, or new discussion. If you think something important is missing, say
so in one sentence at the very end and I will weigh it — but do not draft it. Every
suggestion I have accepted in the last two rounds has cost me a defect somewhere
else.

Praise is not useful to me here. One sentence of overall assessment is plenty.

### What the paper claims

For $k \ge 3$ and $1 \le d_1 < d_2$: the ratio $r_k(d_1,d_2)$ exists **iff**
$d_2 \ge k+1$, with $r_k \le 192 d_2$ above the threshold and non-existence below
it in a strong form. The non-existence half reduces to a bounded subset-sum
covering lemma (Theorem 16.1): every finite $G \subset \mathbb{Z}_{\ge 1}$ with
$|G| \ge 3$, $\gcd(G) = 1$, $\max(G) = M$ admits a multiset of at most $M-1$ of its
elements whose subset sums contain $M$ consecutive integers. The dichotomy is
formalised in Lean 4, `sorry`-free, three standard axioms, no `native_decide`.

### Where the risk actually is: the repairs made last round

The previous pass found five defects. **Every one was in recently edited peripheral
prose, and three were in text added by the two commits before it.** None was on the
critical path. The repairs below are therefore the newest and least-checked text in
the paper, and on past form this is where the next defect will be. **Spend most of
your effort here.**

1. **Table 1, the Lev [Lev97] row, was rewritten.** It previously claimed the
   union-vs-single-multiset separation blocks recovery of $M-1$ "even up to a
   constant". That was false and has been withdrawn. It now says: the bridge (take
   $k$ copies of each element, whose subset sums then contain all of $kA$) gives a
   single multiset of size $k|G| \le 3(M-1)$ at $k = 2\kappa$, so [Lev97] yields a
   linear bound — weaker than the elementary $2M-3$ of Lemma 15.4 — and neither
   reaches $M-1$. Check every quantity in that sentence, and check the row is now
   consistent with §1.8's surrounding text.
2. **Example 16.2's parenthetical was withdrawn, not repaired.** It now reads
   "(Equality in fact holds, but we need only the upper bound and do not prove it.)"
   Two successive attempts to prove that lower bound both introduced defects, so it
   is now an unproved assertion, deliberately. Is asserting it without proof
   defensible here, and is the equality actually true?
3. **§26.3 now names five obligations, not four** (T1, T2, B1, B2, B3), "two for
   Case T and three for Case B". Check the heading, the opening count, the list, the
   closing tally, Table 2's caption, and Table 2's Case-B row all agree — the last
   round they did not.
4. **Obligation B2's condition was relabelled.** $Y + Z \le a-1$ is now called the
   box-size condition and cites the remark following Lemma 17.5 (previously it said
   "frame-merge condition" and cited Remark 17.4, which concerns
   $V' - C' \ge a - 1$, a different hypothesis in a different lemma). Check the
   naming and the cross-reference are now right, and that no other place in the
   paper confuses the two conditions.
5. **§25.1's second extremal family was weakened.** It now claims only the Case-L
   upper bound $m(\{M-2,M-1,M\}) \le M-1$ for all $M$, plus equality verified for
   $M \le 20$, and explicitly declines to assert the general lower bound. Check that
   nothing nearby still asserts two proved families at every maximum.
6. **§26's opening ledger** now lists five load-bearing finite items rather than
   four, including base minimality. Check it matches §26.3.

### Two findings from last round that were not defects

One reviewer reported that Lemma 15.4 reads "$H+g \notin H$" and that Lemma 21.1 and
Example 21.2 read "$k < Z$" and "$k < 4$". The text reads $H + g \not\subseteq H$,
$k \le Z$ and $k \le 4$ respectively, and has throughout. If you find yourself about
to report either, please quote the line you are looking at.

### Verified clean last round — do not redo without reason

All reported sound, several with independent reimplementations of the finite layer:
Lemma 15.4's greedy proof; Proposition 25.1; clause 17.3(d) at $g = 1$ and Case L's
three sub-cases; the grading of Lemma 18.2 and §24's lexicographic recursion; the
exhaustiveness of T1/T2/B1/B2/B3; §1.8's monotonicity argument and $r_2(a,2a) = 2$;
Proposition 14.6 and the palindrome/border/period chain; the $G$-walk type
discipline; the six-branch routing; all 350 certificate rows; the 172 Case-T
exceptions with max $a = 29$; the class counts $0,1,6,5,20,17,32,25,72$; base
minimality; and the branch tallies summing to 83,251.

$\max K = 435/11 \approx 39.55$ on line $(e,h) = (10,1)$. **One reviewer got 41 by
reading a ceiling into the definition of $\beta$ that is not there.** If you get 41,
that is why.

Prior agreement is not proof — if you believe any of the above is wrong, say so. But
do not spend effort re-deriving it without a reason.

### Specific claims you can falsify cheaply

Each of these is a concrete assertion. Any one being wrong matters.

- The per-$a$ Case-B class counts sum to 178, and each printed base is the *first*
  Case-B member of its class.
- Every Table-B row satisfies $Y + Z \le a - 1$ (required by the $\lambda$-lift;
  Remark 17.4 shows it cannot be dropped).
- $\max K = 435/11$ on line $(e,h) = (10,1)$, runners-up $(9,2)$ and $(8,3)$.
- Case L's printed $(x,y,z)$ has budget exactly $M-1$ and covers $M$ consecutive
  integers, in all three sub-cases including $a$ even with $g = 1$.
- $m(\{3,4,5\}) = 4$ and $m(\{1,M-1,M\}) = M-1$.
- $r_2(a,2a) = 2$ for $a \ge 2$.

### Format

A numbered list. For each: **location**, **the claim you say is false**, and
**why** — ideally a counterexample, a specific line where an implication fails, or
a computation that disagrees. Mark each `wrong` (the statement is false),
`unsupported` (may be true, but the given argument does not establish it), or
`imprecise` (true as intended, but as written says something else).

Then one line: *is there anything in this paper that is false?* Yes or no, and if
yes, the most serious instance.

I am not asking whether the paper is good, well-organised, appropriately long, or
ready for a particular journal. I have decided those questions. I am asking whether
it is correct.
