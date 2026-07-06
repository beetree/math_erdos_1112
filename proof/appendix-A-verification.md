*Erdős #1112 · [Index](../README.md) · Appendix A*

## Appendix A. Verification

We first isolate the entire finite content of the proof as a single proposition, so the finite
layer is auditable as one statement rather than scattered across this appendix.

**Proposition FV (finite verification).** *The finite certificate set — Table A, Table B, the
Table-B supplement, and the three Case-P witnesses — has the following properties, each a finite,
mechanical check:*

- *(i) every certificate has budget $\le M - 1$;*
- *(ii) the subset sums of every certificate contain $M$ consecutive integers;*
- *(iii) the Case-T line scan ($\mu \le 11$) over $a \le 3000$ produces exactly the listed
  exceptional triples — Table A, together with the $14$ supplementary `tSuppT` rows required by the
  merge-robust variants — and none for $a > 3000$;*
- *(iv) the Case-B base classes ($a \le 11$) are complete;*
- *(v) the $\lambda$-lift (Lemma 3.4) applies to every larger member of each Table-B class.*

*Proof.* (i)–(ii) are direct finite checks: for each row sum the budget, and compute its subset-sum
set by exact arbitrary-precision bitmask, verifying it contains a length-$M$ run (this is where
Lemma 3.2 enters — a mod-$a$ box with $Y + Z \le a - 1$ certifies exactly such a run). (iii)–(iv)
are exhaustive bounded scans — the $a \le 3000$ line scan of Lemma 3.18(i) and the $a \le 11$,
bounded-$b$ class enumeration of §III.8 — made complete by the slope-tail argument of Lemma
3.18(ii) for $a > 3000$ and the descent argument of §III.8 for larger $b$; (v) is Lemma 3.4. Each
of (i)–(v) is reproduced by the two Python scripts of Appendix C and, independently, by Lean kernel
evaluation (Appendix D). Counting: $158$ (Table A) $+\,172$ (Table B main) $+\,30$ (supplement)
$= 360$ rows checked by `certTableA_ok`/`certTableB_ok`, plus the $14$ supplementary `tSuppT` rows of
(iii) checked by `tSuppT_ok` — $374$ kernel-checked rows in all, deduplicating to the $158 + 178$
distinct classes of Appendix B.
$\blacksquare$

The rest of this appendix details the computations behind Proposition FV. The proof of Theorem 3
is computer-assisted in the following precise, finite sense. Three kinds of computation participate:

*(Epistemic note: the outputs quoted in this appendix are the recorded results of running the
two scripts embedded in Appendix C on the stated inputs — i.e., they document what those
scripts produce, and any reader can reproduce them from this document alone. They are claims
about this manuscript's own verification layer; independently written audits by third parties
are a separate matter and are reported, where they exist, in the Attribution section.)*

1. **Finite certificate tables** (Appendix B): 158 + 178 explicit instances of the (proved) frame
   lemma (Lemma 3.2), plus the three explicit Case-P witnesses. Each is checked by exact
   subset-sum computation (arbitrary-precision bitmasks); Lemma 3.4 (a proved statement) extends
   each Table-B certificate to the infinitely many larger members of its class.
2. **Finite scans closing crude constants of proved lemmas**: the T-line scan to $a = 3000$ with
   the slope-tail argument (Lemma 3.18); the small-$a$ corners of the pair families of Lemma 3.12
   ($a < 15$ in this Python layer; §III.4 and Appendix D close them symbolically for $a \ge 8$) and
   of Lemma 3.14 ($a \le 6$); the minimal-alphabet enumeration to $M \le 130$ (Lemmas 3.9/3.10).
3. **End-to-end redundant verification** (not logically required, but performed): every one of
   the **83,251** hard-core triples with $M \le 120$ was covered by its *designated* branch with
   an exactly verified multiset — zero failures — by **two separate implementations**:
   - `sharp6_final.py` (the constructive harness; branch counts at $M \le 120$: G′ 731, D 2392,
     P-small 3, ETAneg 1457, L 1420, G 414, Table A 158, Table B members 1987, T 3268, η-box
     71,421);
   - `sharp_referee_check.py` (a re-implementation that shares no code with the constructive
     harness and reconstructs each designated witness from the lemma statements alone,
     using the exact stated witnesses with no auxiliary searches; identical counts; additionally:
     brute-force re-verification of Lemmas 3.1–3.4 and 3.6–3.8 on thousands of instances, both
     tables re-validated including base-minimality and class-completeness, λ-lift chains walked
     over 29,402 members arithmetically to $M \le 1500$ and 4,574 exactly to $M \le 250$, the
     pair families on all $a \le 120$, the η-box algebra to $a \le 400$ at the worst member
     $M = a + 12$ — monotone in $M$, so this confirms the lemma for all $M$ — and 400 random
     spot checks to $M = 220$: all with zero failures and zero warnings).

   An additional 800 random hard-core triples with $M \in (120, 200]$ were spot-checked against
   the designated branches (zero failures).

   *Scope of the independence.* The two harnesses are independent only in the limited sense that
   `sharp_referee_check.py` shares no code with `sharp6_final.py` and rebuilds each witness from
   the lemma statements; they are **not** independent of the mathematical case split, which is the
   one stated in this paper. Their agreement corroborates the **finite** layer (§4), not the
   asymptotic lemmas, which are established in the text and formalized in Lean.

To re-run: both scripts are pure Python 3 (standard library only, no third-party dependencies);
`python sharp6_final.py 120` and `python sharp_referee_check.py 120` each complete in minutes and
print the branch counts and failure totals shown above. The complete, verbatim source of both
scripts is embedded in **[Appendix C](appendix-C-scripts.md)**, together with the exact commands,
expected output, and runtimes.

**Actual output of the two harnesses (this revision, Python 3.12.7).** `python sharp6_final.py
120` (≈ 45 s) prints:

```
hard core M<=120: 83251 triples
branch usage: {"G'": 731, 'D': 2392, 'P-small': 3, 'ETAneg': 1457, 'Lg': 1420, 'Gt': 414, 'TABLE-line/box': 158, 'TABLE-base/box': 1987, 'Tline': 3268, 'ETA': 71421}

DESIGNATED-BRANCH FAILURES (must be 0): 0

TABLE entries: 2145
```
(followed by the 2145 explicit table certificates it emits). `python sharp_referee_check.py 120`
(≈ 110 s) prints, in full:

```
loaded tables: A=158 entries, B(+supp)=178 classes

== PART 0: machinery brute-force (Lemmas I, II, III, IV) ==
  Lemma I: 1476 instances, 0 failures
  Lemma II: 1223 nonvacuous instances, 0 failures
  Lemma III: 3288 sub-checks, 0 failures
  Lemma IV: 1224 lift steps verified exactly, 0 failures
== PART 1: reduction lemmas L1, L2, L3 (independent re-check) ==
  L1: 6412 instances, 0 failures
  L2: 785 instances, 0 failures
  L3: 4018 instances, 0 failures
== PART 2: MAIN — decision tree, all hard-core triples M <= 120 ==
  hard-core triples: 83251 (write-up claims 83,251 at Mmax=120)
  branch counts: {"G'": 731, 'D': 2392, 'P-small': 3, 'ETAneg': 1457, 'L': 1420, 'Gt': 414, 'TableA': 158, 'TableB': 1987, 'Tline': 3268, 'ETA': 71421}
  P-small triples (write-up: 'a<=6 verified range', not listed): [(3, 7, 8), (4, 9, 11), (5, 12, 13)]
== PART 3: table certificates ==
  Table A: 158 entries checked (claimed 158), invalid: 0
  Table B(+supp): 178 classes checked, invalid: 0
  Table B completeness: 0 missing classes
== PART 4: T-line scan (mu<=11) to a=3000 + rigorous linear tail ==
  scan failures: 158, max a = 29 (claimed: 158, max 29)
  min tail margin at a=3000 over lines: 995.0 (slope argument: budget slope <= 2/3 < 1, so margin grows for a > 3000)
== PART 5: lambda-lift chains for all Table B classes ==
  lift members: 29402 arithmetic (to M<=1500), 4574 exact (to M<=250), failures 0
  (unbounded-lambda safety: budget step <= Y+Z+1 <= a = target step; proved Lemma IV)
== PART 6: pair families G'(r=3), G_t(r=4) uniform witnesses, all a <= 120 ==
  G' members a<=120: 2192, failures 0
  G_t members a<=120: 2133, failures 0
  G' reach-algebra scan a in [15,400]: 0 failures
  G_t reach-algebra scan a in [15,400]: 0 failures
== PART 7: eta-box algebra (sigma bound + budget threshold), a <= 400 ==
  sigma/budget/coverage scans: 0 failures (these prove Lemma E for ALL M >= a+12, since the check is monotone in M)
== PART 8: L4 / minimal alphabets |G| >= 4 ==
  minimal 4-alphabets M<=130 (d-structure): 12: [(30, 42, 70, 105), (30, 70, 84, 105), (30, 70, 105, 126), (42, 60, 70, 105), (42, 70, 90, 105), (42, 70, 105, 120), (60, 70, 84, 105), (60, 70, 105, 126), (70, 84, 90, 105), (70, 84, 105, 120), (70, 90, 105, 126), (70, 105, 120, 126)]
  minimal 4-alphabets M<=110 (brute force):   6: [(30, 42, 70, 105), (30, 70, 84, 105), (42, 60, 70, 105), (42, 70, 90, 105), (60, 70, 84, 105), (70, 84, 90, 105)]
  minimal |G|>=5: impossible for M <= 209 (elements >= 2*3*5*7 = 210)
    (30, 42, 70, 105): delta=7, H=[6, 10, 15], budget 19 vs M-1=104, covers=True
    (30, 70, 84, 105): delta=7, H=[10, 12, 15], budget 19 vs M-1=104, covers=True
    (30, 70, 105, 126): delta=7, H=[10, 15, 18], budget 21 vs M-1=125, covers=True
    (42, 60, 70, 105): delta=5, H=[12, 14, 21], budget 19 vs M-1=104, covers=True
    (42, 70, 90, 105): delta=5, H=[14, 18, 21], budget 21 vs M-1=104, covers=True
    (42, 70, 105, 120): delta=5, H=[14, 21, 24], budget 23 vs M-1=119, covers=True
    (60, 70, 84, 105): delta=7, H=[10, 12, 15], budget 22 vs M-1=104, covers=True
    (60, 70, 105, 126): delta=7, H=[10, 15, 18], budget 23 vs M-1=125, covers=True
    (70, 84, 90, 105): delta=3, H=[28, 30, 35], budget 22 vs M-1=104, covers=True
    (70, 84, 105, 120): delta=3, H=[28, 35, 40], budget 23 vs M-1=119, covers=True
    (70, 90, 105, 126): delta=3, H=[30, 35, 42], budget 23 vs M-1=125, covers=True
    (70, 105, 120, 126): delta=3, H=[35, 40, 42], budget 24 vs M-1=125, covers=True
  L4 failures: 0
== PART 9: random spot checks 120 < M <= 220 ==
  spots verified: 400, failures: 0

================ SUMMARY ================
FATAL/CONSTRUCTION FAILURES: 0
WARNINGS (write-up/bookkeeping): 0
```

**Which steps are hand proofs and which are computer-assisted.** All lemma statements and their
proofs in Parts I–III are hand proofs, with these finite verified components: Table A + Table B +
three witnesses (item 1), and the explicit finite scans (item 2). Part I and Part II contain no
computer-assisted steps (their numerical checks are redundant confirmation only). Every
computer-verified object is listed in this document (Appendix B), so the proof is self-contained
given the ability to check a subset-sum certificate — each individual check being a finite,
mechanical computation.

**Kernel re-checking of the finite layer (Lean).** The formalization (Appendix D) re-verifies the
entire finite layer of this appendix inside the Lean kernel — with no `native_decide` and no
external process — so the Python harnesses above are corroborated, not relied upon. The certificate
tables were transcribed and re-checked as **360 rows**: Table A ($158$), Table B's $172$ main
rows, and a $30$-row supplement. The supplement encodes the base re-basing of §III.8: of its $30$
rows, $24$ coincide with main-table rows and $6$ are genuinely new bases — precisely the six
diagonal $\bar e = h$ classes named in the Case-B remark, whose $\lambda = 0$ member falls to Case
L and must therefore be based one λ-step up. Deduplicated, the tables carry exactly the
$158 + 178$ distinct classes claimed in Appendix B; formalizing them exposed **no** erroneous,
missing, or redundant row. The $a \le 3000$ T-scan of Lemma 3.18(i) is likewise redone as kernel
`decide` sweeps (in $1000$-value chunks), and — as in the Case-T remark — Case T is run through the
two merge-robust staircase variants only, with the $14$ additional budget failures discharged by
decided frame-box rows (`tSuppT`, checked by `tSuppT_ok`) in place of variant B; counting these, the
kernel decides $374$ certificate rows in all ($360$ Table A/B $+\,14$ `tSuppT`), not $360$.



---
◀ [Part IV — Assembly](04-assembly.md) · **Next ▶** [Attribution & status](attribution-and-status.md) · Related: [Appendix C — scripts](appendix-C-scripts.md), [Appendix D — Lean](appendix-D-lean.md)
