# Final review prompt — falsification pass

Attach `paper/erdos1112.pdf`. Run with several reviewers independently. This prompt
is deliberately narrower than the previous rounds: the goal is to *close*, not to
improve further.

---

## The prompt

This paper has been through four rounds of adversarial review. Each round improved
it, and each round also introduced new defects — of the ten substantive findings in
the last round, seven were in material added by the round before. Fresh prose is
unverified prose, so I am now trying to stop, not to keep polishing.

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

### Where the risk actually is: material new to this draft

These are the things written or changed most recently. They have had the least
scrutiny, and on past form this is where a defect will be. **Please spend most of
your effort here.**

1. **Lemma 15.4 has a new proof** (greedy residue collection) which drops the old
   hypothesis that some $c \in G$ is coprime to $\min G$. Check the greedy argument
   terminates in $\le a-1$ steps, that the subgroup argument is right, and that the
   final count $|R| + x \le a + M - 1$ holds. This proof was written this week.
2. **Proposition 25.1 is new**: $m(\{1, M-1, M\}) = M-1$ for all $M \ge 3$. The
   lower bound argues that all subset sums lie in $sM + [-j, i]$ and that if
   $i+j+1 < M$ some residue class mod $M$ is missed. Check that.
3. **Staircase clause 17.3(d) was restated for $g \ge 1$** (it said $g \ge 2$). The
   previous draft cited it from Case L on an infinite family with $g = 1$, which was
   a real defect. Check that (d)'s proof is genuinely valid at $g = 1$ and that the
   degeneration described is right.
4. **Lemma 18.2 was regraded** to "if SHARP holds for every irreducible alphabet of
   maximum $\le M$, then for every alphabet of maximum $\le M$", and §24 now states
   the recursion as lexicographic on $(\max G, |G|)$. Check the grading is sound and
   that no appeal raises the pair.
5. **Obligation B3 was added** to §26.3 (minimality of the Case-B bases). Check the
   decomposition T1/T2/B1/B2/B3 is now genuinely exhaustive — is there a sixth?
6. **§1.8's monotonicity argument** ($d_2 \le d_2' \Rightarrow r_k(d_1,d_2') \le
   r_k(d_1,d_2)$, hence $r_2(a,2a) = 2$ with Chen). A previous draft got this wrong
   in the opposite direction and claimed a false novelty. Check it is right now.
7. **Example 16.2's parenthetical lower bound** for $m(\{1,2,M\}) = \lceil M/2
   \rceil$. It is compressed and I am least confident in it.
8. **The Lev 1997 row of Table 1.** Corrected against the verbatim statement. The
   separation now claimed is that $kA$ (with $0 \in A$) is a *union* over multisets
   of size $\le k$, while $m(G)$ needs a *single* multiset. Does that separation
   actually hold, and does it block deriving my theorem from Lev's even with a
   worse constant?

### What has already been checked — please do not redo these

Reported sound by multiple independent readers, several with their own
reimplementations of the finite layer:

- Proposition 14.6, the $k$ even, $d_2 = k$ boundary case, and Lemma 14.5's
  palindrome/border/period chain.
- The rescaling type discipline (Definition 9.2, $G$-walks): no statement applied
  after rescaling assumes $d_1$.
- Exhaustiveness of the six-branch routing over the hard core.
- All 350 certificate rows (budget and coverage), the 172 Case-T exceptions, the
  178 Case-B class counts $0,1,6,5,20,17,32,25,72$, and the branch tallies summing
  to 83,251.
- $\max K = 435/11 \approx 39.55$ over the 50 Case-T lines. **One reviewer got 41
  here by reading a ceiling into the definition of $\beta$ that is not there.** If
  you get 41, that is why.

If you believe any of the above *is* wrong, say so — prior agreement is not proof.
But do not spend effort re-deriving them without reason.

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
