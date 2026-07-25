# Expert review prompt — round 3 (post-revision readiness)

Attach `paper/erdos1112.pdf`. Run with several experts independently; do not show
them each other's reports.

---

## The prompt

I am asking you to referee a paper as if for the *Electronic Journal of
Combinatorics*, and to tell me whether it is ready to submit. Please be exhaustive
and blunt. I would much rather read a hard report now than a rejection later.

### What the paper is

It resolves Erdős Problem 1112: for $k \ge 3$ and $1 \le d_1 < d_2$, the ratio
$r_k(d_1,d_2)$ exists **iff** $d_2 \ge k+1$, with $r_k \le 192\,d_2$ above the
threshold and non-existence below it in a strong form. The non-existence half
reduces, through a word-combinatorial analysis of the gap sequence, to a new
bounded subset-sum covering lemma (Theorem B / "SHARP"): every finite
$G \subset \mathbb{Z}_{\ge 1}$ with $|G| \ge 3$ and $\gcd(G) = 1$ admits a multiset
of at most $\max(G) - 1$ of its elements whose subset sums contain $\max(G)$
consecutive integers.

The full dichotomy is formalised in Lean 4: `sorry`-free, three standard axioms, no
`native_decide`. There is a finite certificate layer of 350 rows, printed in full in
Appendix E.

**The paper is deliberately unconventional.** It is ~100 pages; it builds its
prerequisites in the text; it separates the mechanism of each construction from the
estimates that pay for it; it is illustrated throughout; and it is written in plain
language rather than compressed prose. §1.1 states the case for that choice and what
it costs. This is a considered decision, not inexperience — but it is exactly the
kind of decision a referee should push back on if it is not working, so please do
push, while labelling such comments as *form* rather than *correctness* so I can
weigh them separately.

### Status you should know

- The proof has been publicly claimed on erdosproblems.com since 6 July 2026 and has
  not been challenged.
- Thomas Bloom verified on 13 July that the Lean statement is a correct formalisation
  of the problem and that the development compiles with no `sorry`. He explicitly did
  **not** check the mathematics.
- An independent reader rebuilt the whole package from scratch on 17 July.
- **No one has yet claimed to have read and understood the mathematical argument of
  Parts II–IV.** That is what I am asking you for.
- The paper has already been through three rounds of expert review, and this draft
  incorporates all of the resulting changes. Do not assume anything is deliberate
  just because it survived earlier rounds.

### What I most want from you

**1. Is it correct?** This is the whole question. Appendix B ("A referee's guide")
names the five places I believe the proof is most likely to be wrong. Please attack
them directly, and tell me if you think my ranking is wrong:

  - Proposition 14.6, the boundary case $k$ even and $d_2 = k$, where the sweep
    gives width $k-2$ and needs $k-1$, and a separate border–period argument closes
    the gap. Zero slack here.
  - Obligation **T1**, completeness of the Case-T scan: a hand calculation closes
    $a \ge 3000$ uniformly ($K \le 40$ over 50 lines), an exhaustive enumeration
    closes the rest.
  - The type discipline around rescaling. Lemma 9.5 divides all gaps by $g > 1$,
    destroying the lower bound $d_1$; Definition 9.2 (*G*-walk) exists to keep this
    honest. **This was a genuine defect found in the last review round and fixed in
    this draft — please check the fix rather than trusting it.** Specifically: does
    any statement applied after rescaling still secretly assume $d_1$?
  - The strong induction in Theorem B, which has two recursive appeals (Lemmas 18.8
    and 18.2). If either failed to go to a strictly smaller $\max(G)$, Part IV would
    be circular.
  - Exhaustiveness of the six-branch routing over the hard core.

If you find a real error, that is the single most valuable thing you can give me;
please state it as precisely as you can, ideally with a counterexample or the exact
line where the implication fails.

**2. Is the new material doing its job?** The following are new in this draft and
have never been reviewed. Please treat them as unproven:

  - §25.1, open problems (four questions). Are any of them already answered in the
    literature, or trivially answerable? Are they the *right* questions?
  - Appendix B, the referee's guide, including the claim that a full audit is 40–50
    hours. Is that estimate honest, or self-serving?
  - §26.3, the four named finite obligations (T1, T2, B1, B2). Is that decomposition
    complete — is there a fifth obligation I have not named?
  - §26.2, on what the three implementations' agreement is and is not worth.
  - §1.9's comparison table against the literature (see 4 below).
  - The title and abstract.

**3. Is it publishable at EJC, and at this length?** Concretely:
  - Would you recommend accept / minor / major / reject, and why?
  - Is ~100 pages defensible for this result at this venue, or should it be split
    (e.g. the subset-sum lemma as a standalone paper) or compressed?
  - **If you would cut:** name the specific sections you would remove and say what
    is lost. I have resisted cutting so far and would like that resistance tested
    against a concrete list rather than a general feeling.
  - Does the plain-language register help or hurt with a professional readership? Be
    honest if it reads as padded or condescending — that is a failure mode I am
    actively worried about.

**4. The novelty claim.** §1.9 argues Theorem B appears to be new, with a table
stating which hypothesis separates each nearest known result. Do you know of a
result that implies it, even with a worse constant? Is any row of that table
mischaracterised? I am told the likeliest hiding place is the numerical-semigroup
literature (Apéry sets, factorization-length sets), which I have not searched
properly.

**5. Anything you would be embarrassed to see in print.** Trivial lemmas stated with
ceremony, notation that collides, figures that mislead, a proof that is really a
restatement, claims stated more strongly than the evidence supports. Say so plainly.

### Format for your report

Give me a numbered list of findings. For each:

- **Severity**: `blocking` (wrong, or would sink the submission) / `major` (should
  fix before submitting) / `minor` (worth fixing) / `optional` (taste).
- **Type**: `correctness` / `completeness` / `exposition` / `form` / `scholarship`.
- **Location**: section, theorem number, or page.
- **The finding**, stated so I can act on it without guessing what you meant.
- **What you would do about it**, concretely.

Then a short overall verdict: is this ready to submit to EJC as it stands, ready
after specified fixes, or not ready — and if not ready, what is the single thing
standing in the way.

Do not soften anything. If parts of the paper are good, one sentence saying so is
plenty; spend the rest of your effort on what is wrong.
