*Erdős #1112 · [Index](../README.md) · Appendix C*

> **Live scripts.** This file embeds the two Python harnesses, which are still current. The prose
> commentary around them may lag the paper ([`paper/erdos1112.tex`](../paper/erdos1112.tex)), which
> is authoritative for the mathematics.


## Appendix C. Verification scripts (complete source)

This appendix embeds the complete, verbatim source of the two verification harnesses referenced
in Appendix A, so that the proof of Theorem 3 (SHARP) is reproducible from this document alone. The
data file `probes2/sharp_tables.txt` (the machine-readable form of Tables A and B of Appendix B),
read by the referee checker, is reproduced in §C.3 below.

**Environment.** Python 3.12.7 (any CPython ≥ 3.8 works; the scripts use only the standard library
— `sys`, `os`, `re`, `random`, `math`, `itertools`, `functools`, `collections` — and Python's
arbitrary-precision integers for the bitmask subset-sum computations). No third-party packages, no
network access, no compilation.

**Exact run commands** (save the two scripts below, plus `probes2/sharp_tables.txt` from §C.3, into one directory):

```
python sharp6_final.py 120
python sharp_referee_check.py 120
```

The single argument is `Mmax` (default 120). `sharp_referee_check.py` reads
`probes2/sharp_tables.txt` relative to its own location; create that file from the block in §C.3 if
running outside the repository.

**Approximate runtimes (Python 3.12.7, commodity laptop):** `sharp6_final.py 120` ≈ 45 s;
`sharp_referee_check.py 120` ≈ 110 s. Runtime grows with `Mmax` (dominated by the exact
bitmask subset-sum checks over all hard-core triples).

**Expected output.** The exact stdout of both commands is reproduced in Appendix A. The
load-bearing lines are: `sharp6_final.py` prints `hard core M<=120: 83251 triples`, the branch-usage
table `{"G'": 731, 'D': 2392, 'P-small': 3, 'ETAneg': 1457, 'Lg': 1420, 'Gt': 414,
'TABLE-line/box': 158, 'TABLE-base/box': 1987, 'Tline': 3268, 'ETA': 71421}`, and
`DESIGNATED-BRANCH FAILURES (must be 0): 0`; `sharp_referee_check.py` prints the same branch counts
(with tags `L`/`TableA`/`TableB` in place of `Lg`/`TABLE-line`/`TABLE-base`) and ends with
`FATAL/CONSTRUCTION FAILURES: 0` and `WARNINGS (write-up/bookkeeping): 0`. The branch counts sum to
83,251:
$$731 + 2392 + 3 + 1457 + 1420 + 414 + 158 + 1987 + 3268 + 71421 = 83{,}251.$$

### C.1 `sharp6_final.py`

```python
#!/usr/bin/env python3
"""FINAL decision-tree harness for (SHARP) hard core - mirrors the write-up.

Decision tree for hard-core (a,b,M) [gcd(a,b)=1, e=b-a>=1, h=M-b in [1,a-2]]:
 1. a | M              -> Lemma D    (half-price ladder)
 2. a | b+M:
    2a. M < 2a         -> Lemma G'   (r=3 pair family, witness (2,~(M-3)/2,~))
    2b. M = 2a+t       -> Lemma Gt   (r=4 pair family, witness (3,~(M-4)/2,~))
    2c. M >= 2a+4      -> Lemma ETAneg (balanced box (Y,Z), Y+Z=a-1)
    2d. else           -> TABLE
 3. e == h (=g)        -> Lemma Lg   witness (floor((a-2)/2)+2g, 1, ceil((a-2)/2))
 4. a>=12 and mu>=12   -> Lemma ETA  (t=min(eta,a-eta) box, threshold proved)
 5. mu<=11             -> Lemma T-line (g-phase staircase, exact inequality);
                          failures -> TABLE
 6. a<=11, mu>=12      -> base TABLE (certified mod-a box) + lambda-lift
Verify: every branch's constructed multiset covers M consecutive integers
(exact bitmask), budget <= M-1. Output: any triple where the designated
branch FAILS -> table entries. Zero unexplained failures required.
"""
import sys
from math import gcd, ceil
from collections import Counter

def cover_check(a, b, M, x, y, z):
    if min(x, y, z) < 0:
        return False
    mask = 1
    for v in [a] * x + [b] * y + [M] * z:
        mask |= mask << v
    best = run = 0
    while mask:
        if mask & 1:
            run += 1
            if run > best:
                best = run
        else:
            run = 0
        mask >>= 1
    return best >= M

def lemma_D(a, b, M):
    q = M // a
    xeff = ceil((M - 1 + (a - 1) * b) / a)
    best = None
    for z in range(0, xeff // q + 2):
        x = max(q - 1, xeff - q * z)
        n = (a - 1) + x + z
        if best is None or n < best[0]:
            best = (n, x, z)
    n, x, z = best
    return (x, a - 1, z)

def lemma_pair(a, b, M, r):
    yz = M - r
    y = (yz + 1) // 2
    for dy in (0, -1, 1, -2, 2):
        ms = (r - 1, y + dy, yz - y - dy)
        if ms[2] >= 0 and cover_check(a, b, M, *ms):
            return ms
    return None

def lemma_etaneg(a, b, M):
    best = None
    Y0 = round((a - 1) * M / (b + M))
    for Y in {max(0, Y0 - 1), Y0, min(a - 1, Y0 + 1), (a - 1) // 2, a // 2}:
        Z = a - 1 - Y
        if Z < 0:
            continue
        reps = {}
        for j in range(Y + 1):
            for k in range(Z + 1):
                v = j * b + k * M
                rr = v % a
                if rr not in reps or v < reps[rr]:
                    reps[rr] = v
        if len(reps) < a:
            continue
        S = max(reps.values())
        x = ceil((M - 1 + S) / a)
        n = x + Y + Z
        if n <= M - 1 and (best is None or n < best[0]):
            best = (n, (x, Y, Z))
    return best[1] if best else None

def lemma_Lg(a, g):
    return ((a - 2) // 2 + 2 * g, 1, (a - 1) // 2 if (a - 2) % 2 else (a - 2) // 2)

def lemma_eta(a, b, M):
    ebar, mubar = b % a, M % a
    eta = (mubar * pow(ebar, -1, a)) % a
    t = min(eta, a - eta)
    Z = ceil((a - t) / t)
    reps = {}
    for j in range(t):
        for k in range(Z + 1):
            v = j * b + k * M
            rr = v % a
            if rr not in reps or v < reps[rr]:
                reps[rr] = v
    if len(reps) < a:
        return None
    S = max(reps.values())
    x = ceil((M - 1 + S) / a)
    return (x, t - 1, Z)

def lemma_Tline(a, b, M):
    """g-phase staircase, x=c+g variant (proved) + g=1 two-frame variants."""
    e, h = b - a, M - b
    mu = e + h
    g = gcd(e, mu)
    e1, m1 = e // g, mu // g
    C1 = (e1 - 1) * (m1 - 1)
    y = m1 - 1
    cands = []
    if g == 1:
        # variant A (x=c+1): W >= max(a,mu)-1+2C
        zA = max(e1 - 1, ceil((max(a, mu) - 1 + 2 * C1 - y * e1) / m1))
        cands.append((y + zA + 1, y, zA))
        # variant B (x=c): W >= a+C+max(C,1)-1 and W >= mu+2C-1
        need = max(a + C1 + max(C1, 1) - 1, mu + 2 * C1 - 1)
        zB = max(e1 - 1, ceil((need - y * e1) / m1))
        cands.append((y + zB, y, zB))
    else:
        # solid-run variant: V'-C' >= a-1 (phase-c double frame) with run
        # [(c+g-1)a+gC', (c+g)a+gV'] hmm -> use conservative:
        # g(V'-C') >= ga+mu-1  (union of single frames per phase)
        z1 = max(e1 - 1, ceil((a + ceil((mu - 1) / g) + 2 * C1 - y * e1) / m1))
        cands.append((y + z1 + g, y, z1))
    best = None
    for ms in cands:
        n = sum(ms)
        if n <= M - 1 and cover_check(a, b, M, *ms):
            if best is None or n < best[0] + best[1] + best[2]:
                best = ms
    return best

def cert_box(a, b, M):
    """table certificate: minimal mod-a box, Y+Z<=a-1 (lift-compatible)."""
    best = None
    cap = min(2 * a + 4, M)
    for Y in range(0, cap):
        for Z in range(0, cap - Y):
            if Y + Z > a - 1:
                continue
            reps = {}
            for j in range(Y + 1):
                for k in range(Z + 1):
                    v = j * b + k * M
                    r = v % a
                    if r not in reps or v < reps[r]:
                        reps[r] = v
            if len(reps) == a:
                S = max(reps.values())
                x = ceil((M - 1 + S) / a)
                n = x + Y + Z
                if n <= M - 1 and (best is None or n < best[0]):
                    best = (n, (x, Y, Z))
                break
    return best[1] if best else None

def cert_any(a, b, M):
    """last resort: any witness with budget <= M-1 (small search)."""
    tgt = M - 1
    for x in range(tgt + 1):
        for y in range(tgt + 1 - x):
            z = tgt - x - y
            if cover_check(a, b, M, x, y, z):
                return (x, y, z)
    return None

def main():
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    tot = 0
    tags = Counter()
    table = []
    failures = []
    for a in range(3, Mmax):
        for b in range(a + 1, Mmax):
            if gcd(a, b) != 1:
                continue
            for M in range(b + 1, min(a + b - 1, Mmax + 1)):
                e, h = b - a, M - b
                if h > a - 2:
                    continue
                tot += 1
                mu = e + h
                ms, tag = None, None
                if M % a == 0:
                    ms, tag = lemma_D(a, b, M), 'D'
                elif (b + M) % a == 0:
                    r = (b + M) // a
                    P_SMALL = {(3, 7, 8): (4, 2, 1), (4, 9, 11): (4, 3, 3),
                               (5, 12, 13): (4, 4, 4)}
                    if (a, b, M) in P_SMALL:
                        ms, tag = P_SMALL[(a, b, M)], 'P-small'
                    elif M < 2 * a:
                        ms, tag = lemma_pair(a, b, M, 3), "G'"
                    elif r == 4:
                        ms, tag = lemma_pair(a, b, M, r), 'Gt'
                    else:
                        ms, tag = lemma_etaneg(a, b, M), 'ETAneg'
                        if ms is None:
                            ms, tag = lemma_pair(a, b, M, r), 'Gt*'
                elif e == h:
                    ms, tag = lemma_Lg(a, e), 'Lg'
                elif a >= 12 and mu >= 12:
                    ms, tag = lemma_eta(a, b, M), 'ETA'
                elif mu <= 11:
                    ms, tag = lemma_Tline(a, b, M), 'Tline'
                    if ms is None:
                        tag = 'TABLE-line'
                else:
                    tag = 'TABLE-base'
                if ms is not None:
                    n = sum(ms)
                    if n <= M - 1 and cover_check(a, b, M, *ms):
                        tags[tag] += 1
                        continue
                    else:
                        failures.append((a, b, M, tag, ms))
                        continue
                # table route
                cb = cert_box(a, b, M)
                if cb:
                    table.append((a, b, M, tag, 'box', cb))
                    tags[tag + '/box'] += 1
                else:
                    w = cert_any(a, b, M)
                    if w:
                        table.append((a, b, M, tag, 'wit', w))
                        tags[tag + '/wit'] += 1
                    else:
                        failures.append((a, b, M, tag, None))
    print(f"hard core M<={Mmax}: {tot} triples")
    print("branch usage:", dict(tags))
    print(f"\nDESIGNATED-BRANCH FAILURES (must be 0): {len(failures)}")
    for f in failures[:30]:
        print("   ", f)
    print(f"\nTABLE entries: {len(table)}")
    for t in table:
        print("   ", t)

if __name__ == "__main__":
    main()
```

### C.2 `sharp_referee_check.py`

```python
#!/usr/bin/env python3
"""HOSTILE-REFEREE independent checker for (SHARP)  [Erdos #1112, sharp1112.md].

Written from scratch; deliberately does NOT import or mirror sharp6_final.py.
For every hard-core triple M <= 120 it takes the construction DESIGNATED BY THE
PROOF TEXT (exact stated witnesses -- no searches, no perturbations), builds the
multiset, computes exact subset sums, and checks:
    budget <= M-1   and   subset sums contain >= M consecutive integers.
Plus: brute-force checks of Lemmas I/II/III/IV, L1/L2/L3, L4 + minimal-alphabet
enumeration (two independent methods), Table A/B certificate verification,
T-line scan to a=3000 with a rigorous linear tail bound, lambda-lift chains,
eta-box algebra scan, and random spot checks 120 < M <= 220.

Usage: python sharp_referee_check.py [Mmax=120]
"""
import sys, os, re, random
from math import gcd, ceil
from itertools import combinations, combinations_with_replacement
from functools import reduce
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
TABLES = os.path.join(HERE, "probes2", "sharp_tables.txt")

FAIL = []          # fatal mismatches (proof-designated construction fails)
WARN = []          # write-up gaps / bookkeeping problems (not construction failures)

def report(kind, msg):
    (FAIL if kind == "FAIL" else WARN).append(msg)
    print(f"  ** {kind}: {msg}")

# ---------------------------------------------------------------- primitives
def sums_mask(ms):
    m = 1
    for v in ms:
        m |= m << v
    return m

def max_run(mask):
    best = run = 0
    while mask:
        if mask & 1:
            run += 1
            if run > best:
                best = run
        else:
            run = 0
        mask >>= 1
    return best

def covers(a, b, M, x, y, z):
    if min(x, y, z) < 0:
        return False
    return max_run(sums_mask([a]*x + [b]*y + [M]*z)) >= M

def box_reps(a, b, M, Y, Z):
    """minimal-height representative per residue class mod a in box j<=Y,k<=Z."""
    reps = {}
    for j in range(Y + 1):
        for k in range(Z + 1):
            v = j*b + k*M
            r = v % a
            if r not in reps or v < reps[r]:
                reps[r] = v
    return reps

def gcdl(xs):
    return reduce(gcd, xs)

# ------------------------------------------------- designated constructions
def des_D(a, b, M):
    """Case D, a|M. y=a-1 copies of b; optimal (x,z) with x>=q-1, x+qz>=x_eff.
    NOTE: x_eff = ceil((M-1+(a-1)b)/a) = q + b - floor((b+1)/a), which is the
    write-up's closed form (Lemma 3.11, with the FLOOR; an earlier draft's
    ceil((b+1)/a) was off by one when a∤(b+1) and has been corrected)."""
    q = M // a
    xeff = ceil((M - 1 + (a - 1) * b) / a)
    best = None
    for z in range(0, xeff // q + 2):
        x = max(q - 1, xeff - q * z)
        if best is None or x + z < best[0] + best[1]:
            best = (x, z)
    x, z = best
    return (x, a - 1, z)

def des_P1(a, b, M):          # Lemma G'  (r=3):   exact stated witness
    return (2, (M - 2) // 2, (M - 3) // 2)       # (2, ceil((M-3)/2), floor((M-3)/2))

def des_Gt(a, b, M):          # Lemma G   (r=4):   exact stated witness
    return (3, (M - 3) // 2, (M - 4) // 2)       # (3, ceil((M-4)/2), floor((M-4)/2))

def des_ETAneg(a, b, M):      # Lemma N: balanced box, Y=ceil((a-1)/2), Z=floor((a-1)/2)
    Y, Z = (a - 1 + 1) // 2, (a - 1) // 2
    reps = box_reps(a, b, M, Y, Z)
    if len(reps) < a:
        return None
    S = max(reps.values())
    return (ceil((M - 1 + S) / a), Y, Z)

def des_L(a, g):              # Lemma L: (floor((a-2)/2)+2g, 1, ceil((a-2)/2))
    return ((a - 2) // 2 + 2 * g, 1, (a - 1) // 2)

def eta_of(a, b, M):
    ebar = (b - a) % a
    mubar = M % a
    return (mubar * pow(ebar, -1, a)) % a

def des_ETA(a, b, M):         # Lemma E: eta-box
    eta = eta_of(a, b, M)
    assert eta not in (0, 1, a - 1), (a, b, M, eta)
    t = min(eta, a - eta)
    assert 2 <= t <= a // 2
    Z = ceil((a - t) / t)
    reps = box_reps(a, b, M, t - 1, Z)
    if len(reps) < a:
        return None
    S = max(reps.values())
    return (ceil((M - 1 + S) / a), t - 1, Z)

def T_candidates(a, e, h):
    """Section 7 staircase-line variants; returns list of (x,y,z)."""
    mu = e + h
    g = gcd(e, mu)
    e1, m1 = e // g, mu // g
    C1 = (e1 - 1) * (m1 - 1)
    y = m1 - 1
    out = []
    if g == 1:
        zA = max(e1 - 1, ceil((max(a, mu) - 1 + 2 * C1 - y * e1) / m1))
        out.append((y + zA + 1, y, zA))                       # III.b, x=c+1
        need = max(a + C1 + max(C1, 1) - 1, mu + 2 * C1 - 1)
        zB = max(e1 - 1, ceil((need - y * e1) / m1))
        out.append((y + zB, y, zB))                           # III.c, x=c
    else:
        z1 = max(e1 - 1, ceil((a + ceil((mu - 1) / g) + 2 * C1 - y * e1) / m1))
        out.append((y + z1 + g, y, z1))                       # III.d, x=c+g
    return out

# ------------------------------------------------------------- table parsing
def load_tables():
    A, B = {}, {}
    sec = None
    with open(TABLES) as f:
        for line in f:
            if line.startswith("TABLE A"):
                sec = "A"; continue
            if line.startswith("TABLE B-supplement"):
                sec = "BS"; continue
            if line.startswith("TABLE B"):
                sec = "B"; continue
            line = line.strip()
            if sec == "A":
                m = re.match(r"\((\d+),(\d+),(\d+)\) e=\d+ h=\d+: box \((\d+), (\d+), (\d+)\)", line)
                if m:
                    a, b, M, x, Y, Z = map(int, m.groups())
                    A[(a, b, M)] = (x, Y, Z)
            elif sec in ("B", "BS"):
                m = re.match(r"class \(a=(\d+), ebar=(\d+)(?:=h)?(?:, h=(\d+))?\): base \((\d+),(\d+),(\d+)\), box \((\d+), (\d+), (\d+)\)", line)
                if m:
                    a, ebar, h, ba, bb, bM, x, Y, Z = (int(v) if v else None for v in m.groups())
                    if h is None:
                        h = ebar
                    key = (a, ebar, h)
                    if key in B and B[key][:3] != (ba, bb, bM):
                        report("WARN", f"table B duplicate class {key} with different base")
                    B[key] = (ba, bb, bM, x, Y, Z)
    return A, B

# ------------------------------------------------------------ decision tree
def designated(a, b, M, TA, TB):
    """Returns (tag, multiset-or-None, note)."""
    e, h = b - a, M - b
    mu = e + h
    if M % a == 0:
        return "D", des_D(a, b, M), ""
    if (b + M) % a == 0:
        r = (b + M) // a
        if M < 2 * a:
            return "G'", des_P1(a, b, M), ""
        if r == 4:
            return "Gt", des_Gt(a, b, M), ""
        if M >= 2 * a + 4:
            ms = des_ETAneg(a, b, M)
            return "ETAneg", ms, "" if ms else "residue-coverage failed"
        return "P-small", None, f"r={r}, M={M}<2a+4: proof only says 'verified range'"
    if e == h:
        return "L", des_L(a, e), ""
    if a >= 12 and mu >= 12:
        ms = des_ETA(a, b, M)
        return "ETA", ms, "" if ms else "residue-coverage failed"
    if mu <= 11:
        for ms in T_candidates(a, e, h):
            if sum(ms) <= M - 1:
                return "Tline", ms, ""
        if (a, b, M) in TA:
            x, Y, Z = TA[(a, b, M)]
            return "TableA", (x, Y, Z), ""
        return "Tline", None, "budget fails and no Table A entry"
    # a <= 11, mu >= 12
    ebar = e % a
    key = (a, ebar, h)
    if key not in TB:
        return "TableB", None, f"class {key} missing from Table B"
    ba, bb, bM, bx, Y, Z = TB[key]
    if M < bM:
        return "TableB", None, f"member M={M} below class base M={bM} (lift only goes up)"
    if (b - bb) % a != 0 or (M - bM) != (b - bb):
        return "TableB", None, f"member not on class lift ladder from base {(ba,bb,bM)}"
    reps = box_reps(a, b, M, Y, Z)
    if len(reps) < a:
        return "TableB", None, "lifted box loses residue coverage (impossible if base ok)"
    S = max(reps.values())
    return "TableB", (ceil((M - 1 + S) / a), Y, Z), ""

# ==========================================================================
def part_machinery():
    print("== PART 0: machinery brute-force (Lemmas I, II, III, IV) ==")
    # Lemma I
    n = bad = 0
    for al in range(1, 9):
        for be in range(al + 1, 13):
            if gcd(al, be) != 1:
                continue
            C = (al - 1) * (be - 1)
            for x in range(be - 1, be + 5):
                for y in range(al - 1, al + 5):
                    grid = {i * al + j * be for i in range(x + 1) for j in range(y + 1)}
                    n += 1
                    if not all(v in grid for v in range(C, al * x + be * y - C + 1)):
                        bad += 1
                        report("FAIL", f"Lemma I fails ({al},{be},{x},{y})")
    print(f"  Lemma I: {n} instances, {bad} failures")
    # Lemma II (frame)
    rng = random.Random(2026)
    n = bad = 0
    for _ in range(3000):
        nu = rng.randint(2, 20); g1 = rng.randint(1, 35); g2 = rng.randint(1, 35)
        L = rng.randint(2, 40); Y = rng.randint(0, 7); Z = rng.randint(0, 7)
        reps = {}
        for j in range(Y + 1):
            for k in range(Z + 1):
                v = j * g1 + k * g2
                if v % nu not in reps or v < reps[v % nu]:
                    reps[v % nu] = v
        if len(reps) < nu:
            continue
        n += 1
        S = max(reps.values()); x = ceil((L - 1 + S) / nu)
        sm = sums_mask([g1] * Y + [g2] * Z + [nu] * x)
        if not all((sm >> v) & 1 for v in range(S, nu * x + 1)):
            bad += 1
            report("FAIL", f"Lemma II fails ({g1},{g2},{nu},{L},{Y},{Z})")
    print(f"  Lemma II: {n} nonvacuous instances, {bad} failures")
    # Lemma III (a-d)
    n = bad = 0
    for _ in range(1200):
        a = rng.randint(3, 13)
        e = rng.randint(1, 9)
        if gcd(a, e) != 1:
            continue
        h = rng.randint(1, 9)
        mu = e + h
        if h == mu - e == e:                      # allow e==h too; III is general
            pass
        g = gcd(e, mu); e1, m1 = e // g, mu // g
        if m1 < 2:
            continue
        C1 = (e1 - 1) * (m1 - 1)
        y = m1 - 1 + rng.randint(0, 2)
        z = e1 - 1 + rng.randint(0, 3)
        c = y + z
        b, M = a + e, a + mu
        V1 = y * e1 + z * m1 - C1
        # III.a at levels t in [c, x], x = c + extra
        x = c + rng.randint(0, 3)
        for t in range(c, x + 1):
            Ot = {j * e + k * mu for j in range(y + 1) for k in range(z + 1)
                  if max(0, t - x) <= j + k <= t}
            n += 1
            if not all(g * v in Ot for v in range(C1, V1 + 1)):
                bad += 1
                report("FAIL", f"III.a fails a={a} e={e} h={h} y={y} z={z} t={t} x={x}")
        full = None
        if g == 1:
            V, C = V1, C1
            if V - C >= a - 1:                    # III.b with x=c+1
                full = sums_mask([a] * (c + 1) + [b] * y + [M] * z)
                lo, hi = c * a + C, (c + 1) * a + V
                n += 1
                if not all((full >> v) & 1 for v in range(lo, hi + 1)):
                    bad += 1
                    report("FAIL", f"III.b fails a={a} e={e} h={h} y={y} z={z}")
            if V >= a + max(C, 1) - 1:            # III.c with x=c
                full = sums_mask([a] * c + [b] * y + [M] * z)
                lo, hi = c * a + C, (c + 1) * a + V
                n += 1
                if not all((full >> v) & 1 for v in range(lo, hi + 1)):
                    bad += 1
                    report("FAIL", f"III.c fails a={a} e={e} h={h} y={y} z={z}")
        else:
            if gcd(a, g) == 1 and g * (V1 - C1) - (g - 1) * a + 1 >= 1:  # III.d, x=c+g
                full = sums_mask([a] * (c + g) + [b] * y + [M] * z)
                lo, hi = (c + g - 1) * a + g * C1, c * a + g * V1
                n += 1
                if lo <= hi and not all((full >> v) & 1 for v in range(lo, hi + 1)):
                    bad += 1
                    report("FAIL", f"III.d fails a={a} e={e} h={h} y={y} z={z} g={g}")
    print(f"  Lemma III: {n} sub-checks, {bad} failures")
    # Lemma IV (lambda-lift), random chains
    n = bad = 0
    for _ in range(400):
        a = rng.randint(3, 12)
        b = rng.randint(a + 1, 3 * a)
        if gcd(a, b) != 1:
            continue
        M = b + rng.randint(1, max(1, a - 2))
        if M - b > a - 2 or M <= b:
            continue
        best = None
        for Y in range(a):
            for Z in range(a - Y):
                reps = box_reps(a, b, M, Y, Z)
                if len(reps) < a:
                    continue
                S = max(reps.values())
                x = ceil((M - 1 + S) / a)
                if x + Y + Z <= M - 1:
                    best = (Y, Z)
                    break
            if best:
                break
        if not best:
            continue
        Y, Z = best
        for lam in range(8):
            bb, MM = b + lam * a, M + lam * a
            reps = box_reps(a, bb, MM, Y, Z)
            if len(reps) < a:
                bad += 1
                report("FAIL", f"lift loses coverage ({a},{b},{M}) lam={lam}")
                break
            S = max(reps.values())
            x = ceil((MM - 1 + S) / a)
            n += 1
            if x + Y + Z > MM - 1 or not covers(a, bb, MM, x, Y, Z):
                bad += 1
                report("FAIL", f"lambda-lift fails ({a},{b},{M}) lam={lam} box=({Y},{Z})")
                break
    print(f"  Lemma IV: {n} lift steps verified exactly, {bad} failures")

def part_L123():
    print("== PART 1: reduction lemmas L1, L2, L3 (independent re-check) ==")
    n = bad = 0
    for M in range(3, 41):                                   # L1
        for al in range(1, M):
            for c in range(1, M):
                if c == al or gcd(al, c) != 1 or al + c > M - 1:
                    continue
                x = M - al
                sm = sums_mask([al] * x + [c] * (al - 1))
                lo, hi = (al - 1) * c, x * al
                n += 1
                if x + al - 1 > M - 1 or hi - lo + 1 < M or \
                   not all((sm >> v) & 1 for v in range(lo, hi + 1)):
                    bad += 1
                    report("FAIL", f"L1 fails ({al},{c},M={M})")
    print(f"  L1: {n} instances, {bad} failures")
    n = bad = 0
    for M in range(4, 51):                                   # L2
        for al in range(1, M):
            for be in range(al + 1, M + 1):
                if gcd(al, be) != 1 or al + be not in (M, M + 1):
                    continue
                t = 1 if al + be == M else 0
                x, y = be - 1, al - 1 + t
                sm = sums_mask([al] * x + [be] * y)
                n += 1
                if x + y > M - 1 or max_run(sm) < M:
                    bad += 1
                    report("FAIL", f"L2 fails ({al},{be},M={M})")
    print(f"  L2: {n} instances, {bad} failures")
    n = bad = 0
    for M in range(4, 51):                                   # L3
        for a in range(2, M):
            for b in range(a + 1, M):
                d = gcd(a, b)
                if d < 2 or gcd(d, M) != 1:
                    continue
                al, be = a // d, b // d
                C = (al - 1) * (be - 1)
                x, y = be - 1, M - d - be + 1
                n += 1
                if y < al - 1:
                    bad += 1
                    report("FAIL", f"L3 y-requirement fails ({a},{b},M={M})")
                    continue
                L = al * x + be * y - 2 * C + 1
                sm = sums_mask([a] * x + [b] * y + [M] * (d - 1))
                lo = d * C + (d - 1) * M
                hi = d * C + (L - 1) * d
                if x + y + d - 1 > M - 1 or L < M + 1 or hi - lo + 1 < M or \
                   not all((sm >> v) & 1 for v in range(lo, hi + 1)):
                    bad += 1
                    report("FAIL", f"L3 fails ({a},{b},M={M})")
    print(f"  L3: {n} instances, {bad} failures")

def part_tree(Mmax, TA, TB):
    print(f"== PART 2: MAIN — decision tree, all hard-core triples M <= {Mmax} ==")
    tot = 0
    tags = Counter()
    psmall = []
    for a in range(3, Mmax):
        for b in range(a + 1, Mmax):
            if gcd(a, b) != 1:
                continue
            for M in range(b + 1, min(a + b - 1, Mmax + 1)):
                if M - b > a - 2:
                    continue
                tot += 1
                tag, ms, note = designated(a, b, M, TA, TB)
                if tag == "P-small":
                    psmall.append((a, b, M))
                    # finite explicit hole: verify SOME witness exists
                    ok = False
                    for tot_n in range(1, M):
                        for x in range(tot_n + 1):
                            for y in range(tot_n + 1 - x):
                                if covers(a, b, M, x, y, tot_n - x - y):
                                    ok = True
                                    break
                            if ok:
                                break
                        if ok:
                            break
                    tags["P-small"] += 1
                    if not ok:
                        report("FAIL", f"P-small triple ({a},{b},{M}) has NO witness <= M-1")
                    continue
                if ms is None:
                    report("FAIL", f"({a},{b},{M}) branch {tag}: no designated construction ({note})")
                    continue
                x, y, z = ms
                if x + y + z > M - 1:
                    report("FAIL", f"({a},{b},{M}) branch {tag}: budget {x+y+z} > M-1={M-1}")
                    continue
                if not covers(a, b, M, x, y, z):
                    report("FAIL", f"({a},{b},{M}) branch {tag}: multiset {ms} does NOT cover {M} consecutive")
                    continue
                tags[tag] += 1
    print(f"  hard-core triples: {tot} (write-up claims 83,251 at Mmax=120)")
    print(f"  branch counts: {dict(tags)}")
    print(f"  P-small triples (write-up: 'a<=6 verified range', not listed): {psmall}")
    if Mmax == 120 and tot != 83251:
        report("WARN", f"hard-core count {tot} != claimed 83,251")
    return tags

def part_tables(TA, TB):
    print("== PART 3: table certificates ==")
    bad = 0
    for (a, b, M), (x, Y, Z) in TA.items():
        e, h = b - a, M - b
        ok_ctx = gcd(a, b) == 1 and 1 <= h <= a - 2 and e + h <= 11 and \
                 M % a != 0 and (b + M) % a != 0 and e != h
        if not ok_ctx:
            bad += 1
            report("FAIL", f"Table A entry ({a},{b},{M}) is not a T-line hard-core triple")
        reps = box_reps(a, b, M, Y, Z)
        if len(reps) < a or Y + Z > a - 1 or x + Y + Z > M - 1 or \
           a * x < M - 1 + max(reps.values()) or not covers(a, b, M, x, Y, Z):
            bad += 1
            report("FAIL", f"Table A certificate ({a},{b},{M}) box ({x},{Y},{Z}) invalid")
        # entry must genuinely be an exception (else table is padding)
        if any(sum(c) <= M - 1 for c in T_candidates(a, e, h)):
            report("WARN", f"Table A entry ({a},{b},{M}) is NOT actually a T-line failure")
    print(f"  Table A: {len(TA)} entries checked (claimed 158), invalid: {bad}")
    if len(TA) != 158:
        report("WARN", f"Table A has {len(TA)} entries, claimed 158")
    bad = 0
    for (a, ebar, h), (ba, bb, bM, x, Y, Z) in TB.items():
        e = bb - ba
        ok_ctx = ba == a and gcd(a, bb) == 1 and bM - bb == h and e % a == ebar and \
                 (bM - ba) >= 12 and bM % a != 0 and (bb + bM) % a != 0
        if not ok_ctx:
            bad += 1
            report("FAIL", f"Table B base {(a,ebar,h)} -> ({ba},{bb},{bM}) context wrong")
        reps = box_reps(a, bb, bM, Y, Z)
        if len(reps) < a or Y + Z > a - 1 or x + Y + Z > bM - 1 or \
           a * x < bM - 1 + max(reps.values()) or not covers(a, bb, bM, x, Y, Z):
            bad += 1
            report("FAIL", f"Table B certificate {(a,ebar,h)} box ({x},{Y},{Z}) invalid")
    print(f"  Table B(+supp): {len(TB)} classes checked, invalid: {bad}")
    # completeness of Table B: every (a<=11, ebar, h) class that has any branch-B
    # member must be present; smallest-base check
    missing = []
    for a in range(3, 12):
        for ebar in range(1, a):
            if gcd(a, ebar) != 1:
                continue
            for h in range(1, a - 1):
                # class hits branch B iff not D (a|mu-class), not P, some member mu>=12, e!=h member exists
                if (ebar + h) % a == 0 or (2 * ebar + h) % a == 0:
                    continue    # class-invariant D / P
                # find smallest member with mu>=12 and e != h
                lam = 0
                found = None
                while lam < 30:
                    e = ebar + lam * a
                    b, M = a + e, a + e + h
                    if e + h >= 12 and e != h and gcd(a, b) == 1:
                        found = (a, b, M)
                        break
                    lam += 1
                if found is None:
                    continue
                if (a, ebar, h) not in TB:
                    missing.append((a, ebar, h, found))
                else:
                    ba, bb, bM = TB[(a, ebar, h)][:3]
                    if (bM, bb) > (found[2], found[1]):
                        report("FAIL", f"Table B base {(a,ebar,h)}=({ba},{bb},{bM}) is not the smallest branch-B member {found}")
    for m in missing:
        report("FAIL", f"Table B missing class {m[:3]} (first member {m[3]})")
    print(f"  Table B completeness: {len(missing)} missing classes")

def part_Tscan(TA):
    print("== PART 4: T-line scan (mu<=11) to a=3000 + rigorous linear tail ==")
    failures = set()
    worst_margin = {}
    for e in range(1, 11):
        for h in range(1, 11):
            mu = e + h
            if mu > 11 or e == h:
                continue
            g = gcd(e, mu)
            e1, m1 = e // g, mu // g
            for a in range(max(3, h + 2), 3001):
                if gcd(a, e) != 1 or mu % a == 0 or (2 * e + h) % a == 0:
                    continue
                M = a + mu
                if not any(sum(c) <= M - 1 for c in T_candidates(a, e, h)):
                    failures.add((a, a + e, M))
            # rigorous tail: real-valued upper bound on the cheapest variant budget,
            # slope 2/m1 <= 2/3 < 1 = slope of M-1  =>  once satisfied with margin
            # it stays satisfied. Evaluate at a0=3000.
            a0 = 3000
            y = m1 - 1
            C1 = (e1 - 1) * (m1 - 1)
            if g == 1:
                need = max(a0 + C1 + max(C1, 1) - 1, mu + 2 * C1 - 1)
                z_ub = max(e1 - 1, (need - y * e1) / m1 + 1)
                bud_ub = 2 * (y + z_ub)
            else:
                z_ub = max(e1 - 1, (a0 + ceil((mu - 1) / g) + 2 * C1 - y * e1) / m1 + 1)
                bud_ub = 2 * (y + z_ub) + g
            margin = (a0 + mu - 1) - bud_ub
            worst_margin[(e, h)] = margin
            if margin < (a0 * (1 - 2 / m1)) * 0 or margin <= 0:
                report("FAIL", f"T-line ({e},{h}): tail bound not established at a=3000 (margin {margin:.1f})")
    mx = max(a for a, _, _ in failures) if failures else 0
    print(f"  scan failures: {len(failures)}, max a = {mx} (claimed: 158, max 29)")
    if len(failures) != 158 or mx != 29:
        report("WARN" if failures == set(TA) else "FAIL",
               f"T-scan found {len(failures)} exceptions (max a={mx}), claimed 158/29")
    onlyA = set(TA) - failures
    onlyS = failures - set(TA)
    if onlyS:
        report("FAIL", f"T-line exceptions NOT in Table A: {sorted(onlyS)}")
    if onlyA:
        report("WARN", f"Table A entries that are not scan failures: {sorted(onlyA)}")
    print(f"  min tail margin at a=3000 over lines: {min(worst_margin.values()):.1f} "
          f"(slope argument: budget slope <= 2/3 < 1, so margin grows for a > 3000)")

def part_lift(TB):
    print("== PART 5: lambda-lift chains for all Table B classes ==")
    n_arith = n_exact = bad = 0
    for (a, ebar, h), (ba, bb, bM, x0, Y, Z) in sorted(TB.items()):
        if Y + Z > a - 1:
            report("FAIL", f"class {(a,ebar,h)}: Y+Z={Y+Z} > a-1 breaks the lift")
        lam = 0
        while True:
            b, M = bb + lam * a, bM + lam * a
            if M > 1500:
                break
            reps = box_reps(a, b, M, Y, Z)
            if len(reps) < a:
                bad += 1
                report("FAIL", f"class {(a,ebar,h)} member ({a},{b},{M}): box loses coverage")
                break
            S = max(reps.values())
            x = ceil((M - 1 + S) / a)
            n_arith += 1
            if x + Y + Z > M - 1:
                bad += 1
                report("FAIL", f"class {(a,ebar,h)} member ({a},{b},{M}): budget {x+Y+Z} > {M-1}")
                break
            if M <= 250:
                n_exact += 1
                if not covers(a, b, M, x, Y, Z):
                    bad += 1
                    report("FAIL", f"class {(a,ebar,h)} member ({a},{b},{M}): coverage fails")
                    break
            lam += 1
    print(f"  lift members: {n_arith} arithmetic (to M<=1500), {n_exact} exact (to M<=250), failures {bad}")
    print("  (unbounded-lambda safety: budget step <= Y+Z+1 <= a = target step; proved Lemma IV)")

def part_families():
    print("== PART 6: pair families G'(r=3), G_t(r=4) uniform witnesses, all a <= 120 ==")
    n = bad = 0
    for a in range(3, 121):
        for s in range(1, (a - 1) // 2 + 1):
            if gcd(a, s) != 1:
                continue
            b, M = a + s, 2 * a - s
            if not (a < b < M) or M - b > a - 2 or M - b < 1:
                continue
            x, y, z = des_P1(a, b, M)
            n += 1
            if x + y + z > M - 1 or not covers(a, b, M, x, y, z):
                bad += 1
                report("FAIL", f"G' family ({a},{b},{M}): stated witness fails")
    print(f"  G' members a<=120: {n}, failures {bad}")
    n = bad = 0
    for a in range(4, 121):
        for t in range(1, (a - 2) // 2 + 1):
            if gcd(a, t) != 1:
                continue
            b, M = 2 * a - t, 2 * a + t
            if gcd(a, b) != 1 or M - b != 2 * t or 2 * t > a - 2:
                continue
            x, y, z = des_Gt(a, b, M)
            n += 1
            if x + y + z > M - 1 or not covers(a, b, M, x, y, z):
                bad += 1
                report("FAIL", f"G_t family ({a},{b},{M}): stated witness fails")
    print(f"  G_t members a<=120: {n}, failures {bad}")
    # crude reach algebra, arithmetic, a<=400 (write-up claims closure for a>=15)
    bad = 0
    for a in range(15, 401):
        W = (a - 1 + 1) // 2
        for s in range(1, (a - 1) // 2 + 1):
            if gcd(a, s) != 1:
                continue
            M = 2 * a - s
            y, z = (M - 2) // 2, (M - 3) // 2
            if min(y, z) < W:
                bad += 1
            length = 3 * a * min(y, z) - 2 * W * M - 2 * a + 1
            if length < M:
                bad += 1
                report("FAIL", f"G' reach algebra fails at (a={a},s={s})")
    print(f"  G' reach-algebra scan a in [15,400]: {bad} failures")
    bad = 0
    for a in range(15, 401):
        W = (a - 1 + 1) // 2
        for t in range(1, (a - 2) // 2 + 1):
            if gcd(a, t) != 1:
                continue
            M = 2 * a + t
            y, z = (M - 3) // 2, (M - 4) // 2
            if min(y, z) < W:
                bad += 1
            length = 4 * a * min(y, z) - 2 * W * M - 3 * a + 1
            if length < M:
                bad += 1
                report("FAIL", f"G_t reach algebra fails at (a={a},t={t})")
    print(f"  G_t reach-algebra scan a in [15,400]: {bad} failures")

def part_eta_algebra():
    print("== PART 7: eta-box algebra (sigma bound + budget threshold), a <= 400 ==")
    bad = 0
    for a in range(12, 401):
        for t in range(2, a // 2 + 1):
            sig = t + ceil((a - t) / t)
            if 2 * sig > a + 4:
                bad += 1
                report("FAIL", f"sigma bound fails a={a} t={t}: sigma={sig} > (a+4)/2")
            # budget implication with worst member M = a+12, crude S bound:
            M = a + 12
            if sig * (M + a) > a * M + t:
                bad += 1
                report("FAIL", f"eta budget threshold fails a={a} t={t} (M=a+12)")
            if t * (ceil((a - t) / t) + 1) < a:
                bad += 1
                report("FAIL", f"eta-box residue coverage count fails a={a} t={t}")
    print(f"  sigma/budget/coverage scans: {bad} failures "
          "(these prove Lemma E for ALL M >= a+12, since the check is monotone in M)")

def enumerate_minimal4(Mmax):
    """Minimal |G|=4 alphabets via the d-structure theorem:
    d_i := gcd(G\\{g_i}) are pairwise coprime >= 2, and g_i is a multiple of
    P_i := prod_{j!=i} d_j.  So enumerate pairwise-coprime quadruples with all
    P_i <= Mmax and all multipliers."""
    out = set()
    for d1 in range(2, Mmax):
        for d2 in range(d1 + 1, Mmax):
            if gcd(d1, d2) != 1 or d1 * d2 * 4 > Mmax * 1:  # need d3,d4 >= next coprimes
                if gcd(d1, d2) != 1:
                    continue
            if gcd(d1, d2) != 1:
                continue
            for d3 in range(d2 + 1, Mmax):
                if gcd(d1, d3) != 1 or gcd(d2, d3) != 1 or d1 * d2 * d3 > Mmax:
                    continue
                for d4 in range(d3 + 1, Mmax):
                    if gcd(d1, d4) != 1 or gcd(d2, d4) != 1 or gcd(d3, d4) != 1:
                        continue
                    D = d1 * d2 * d3 * d4
                    P = [D // d for d in (d1, d2, d3, d4)]
                    if max(P) > Mmax:
                        continue
                    mults = [range(1, Mmax // p + 1) for p in P]
                    for m1 in mults[0]:
                        for m2 in mults[1]:
                            for m3 in mults[2]:
                                for m4 in mults[3]:
                                    G = tuple(sorted({m1*P[0], m2*P[1], m3*P[2], m4*P[3]}))
                                    if len(G) < 4 or gcdl(G) != 1:
                                        continue
                                    ok = all(gcd(u, v) >= 2 for u, v in combinations(G, 2)) and \
                                         all(gcdl(s) >= 2 for s in combinations(G, 3))
                                    if ok:
                                        out.add(G)
    return sorted(out)

def brute_minimal4(Mmax):
    """Independent brute force (clique method) for cross-checking."""
    nums = list(range(2, Mmax + 1))
    adj = {u: set() for u in nums}
    for u, v in combinations(nums, 2):
        if gcd(u, v) >= 2:
            adj[u].add(v)
    out = []
    for u in nums:
        for v in sorted(adj[u]):
            common_uv = adj[u] & adj[v]
            for w in sorted(common_uv):
                if w <= v:
                    continue
                for t in sorted(common_uv & adj[w]):
                    if t <= w:
                        continue
                    G = (u, v, w, t)
                    if gcdl(G) != 1:
                        continue
                    if all(gcdl(s) >= 2 for s in combinations(G, 3)):
                        out.append(G)
    return sorted(set(out))

def find_H_witness(H, target_run, cap):
    """some multiset from H with run >= target_run and size <= cap (exact search)."""
    H = sorted(H)
    for m in range(1, cap + 1):
        for ms in combinations_with_replacement(H, m):
            if max_run(sums_mask(ms)) >= target_run:
                return list(ms)
    return None

def part_L4():
    print("== PART 8: L4 / minimal alphabets |G| >= 4 ==")
    Mmax = 130
    A1 = enumerate_minimal4(Mmax)
    A2 = brute_minimal4(110)
    A1_110 = [G for G in A1 if G[-1] <= 110]
    print(f"  minimal 4-alphabets M<={Mmax} (d-structure): {len(A1)}: {A1}")
    print(f"  minimal 4-alphabets M<=110 (brute force):   {len(A2)}: {A2}")
    if A1_110 != A2:
        report("FAIL", f"minimal-alphabet enumerations disagree: {A1_110} vs {A2}")
    # |G|>=5 minimal: each element divisible by product of 4 pairwise-coprime
    # d_i >= 2 -> >= 2*3*5*7 = 210 > 130: none in range. (structure argument)
    print("  minimal |G|>=5: impossible for M <= 209 (elements >= 2*3*5*7 = 210)")
    bad = 0
    for G in A1:
        a, M = G[0], G[-1]
        Gp = list(G[1:])
        delta = gcdl(Gp)
        if delta < 2 or gcd(a, delta) != 1:
            bad += 1
            report("FAIL", f"L4 structure fails for {G}: delta={delta}")
            continue
        H = [g // delta for g in Gp]
        MH = max(H)
        wit = find_H_witness(H, MH, MH - 1)     # induction hypothesis (SHARP) for H
        if wit is None:
            bad += 1
            report("FAIL", f"L4: no (SHARP) witness for H={H} (induction input false?)")
            continue
        # Graham fill in H with a' = min(H) up to ell
        ap = min(H)
        ell = ceil((M - 1 + (delta - 1) * a) / delta) + 1
        ms = list(wit)
        run = max_run(sums_mask(ms))
        while run < ell:
            if ap > run:
                bad += 1
                report("FAIL", f"L4 Graham fill stuck for {G}: a'={ap} > run={run}")
                break
            ms.append(ap)
            run += ap
        full = [v * delta for v in ms] + [a] * (delta - 1)
        T = len(full)
        okcov = max_run(sums_mask(full)) >= M
        print(f"    {G}: delta={delta}, H={H}, budget {T} vs M-1={M-1}, covers={okcov}")
        if T > M - 1 or not okcov:
            bad += 1
            report("FAIL", f"L4 construction fails for {G}: budget {T}, covers={okcov}")
    print(f"  L4 failures: {bad}")

def part_spot(TA, TB):
    print("== PART 9: random spot checks 120 < M <= 220 ==")
    rng = random.Random(1112)
    n = bad = 0
    tries = 0
    while n < 400 and tries < 20000:
        tries += 1
        M = rng.randint(121, 220)
        a = rng.randint(3, M - 2)
        b = rng.randint(max(a + 1, M - a + 2), M - 1)
        if b <= a or gcd(a, b) != 1 or M - b > a - 2 or M - b < 1:
            continue
        tag, ms, note = designated(a, b, M, TA, TB)
        if tag == "P-small":
            report("FAIL", f"spot ({a},{b},{M}): P-small beyond verified range!")
            continue
        if ms is None:
            bad += 1
            report("FAIL", f"spot ({a},{b},{M}) branch {tag}: no construction ({note})")
            continue
        x, y, z = ms
        n += 1
        if x + y + z > M - 1 or not covers(a, b, M, x, y, z):
            bad += 1
            report("FAIL", f"spot ({a},{b},{M}) branch {tag}: {ms} fails")
    print(f"  spots verified: {n}, failures: {bad}")

def main():
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    TA, TB = load_tables()
    print(f"loaded tables: A={len(TA)} entries, B(+supp)={len(TB)} classes\n")
    part_machinery()
    part_L123()
    part_tree(Mmax, TA, TB)
    part_tables(TA, TB)
    part_Tscan(TA)
    part_lift(TB)
    part_families()
    part_eta_algebra()
    part_L4()
    part_spot(TA, TB)
    print("\n================ SUMMARY ================")
    print(f"FATAL/CONSTRUCTION FAILURES: {len(FAIL)}")
    for f in FAIL:
        print("  FAIL:", f)
    print(f"WARNINGS (write-up/bookkeeping): {len(WARN)}")
    for w in WARN:
        print("  WARN:", w)

if __name__ == "__main__":
    main()
```

### C.3 `probes2/sharp_tables.txt` (data file read by `sharp_referee_check.py`)

This is the machine-readable form of Tables A and B of Appendix B (plus the Table-B supplement).
`sharp_referee_check.py` parses it to independently re-verify every certificate. Save it as
`probes2/sharp_tables.txt` relative to the checker.

```
TABLE A: mu<=11 T-line exceptions (exhaustive a<=3000; all a<=29), mod-a box certificates (x,Y,Z)
  (4,9,10) e=5 h=1: box (7, 1, 1)
  (4,13,14) e=9 h=1: box (10, 1, 1)
  (5,8,9) e=3 h=1: box (5, 2, 1)
  (5,9,12) e=4 h=3: box (7, 2, 1)
  (5,11,12) e=6 h=1: box (7, 1, 2)
  (5,11,13) e=6 h=2: box (8, 2, 1)
  (5,12,14) e=7 h=2: box (9, 1, 2)
  (5,13,14) e=8 h=1: box (8, 2, 1)
  (5,13,16) e=8 h=3: box (10, 1, 2)
  (6,11,14) e=5 h=3: box (9, 1, 2)
  (6,11,15) e=5 h=4: box (9, 2, 1)
  (6,13,14) e=7 h=1: box (9, 1, 2)
  (6,13,15) e=7 h=2: box (10, 2, 1)
  (6,13,16) e=7 h=3: box (10, 1, 2)
  (7,10,12) e=3 h=2: box (7, 3, 1)
  (7,10,15) e=3 h=5: box (8, 2, 2)
  (7,11,12) e=4 h=1: box (7, 2, 2)
  (7,11,13) e=4 h=2: box (7, 2, 2)
  (7,11,16) e=4 h=5: box (8, 3, 1)
  (7,12,13) e=5 h=1: box (7, 3, 1)
  (7,12,15) e=5 h=3: box (8, 2, 2)
  (7,13,17) e=6 h=4: box (9, 3, 1)
  (7,13,18) e=6 h=5: box (9, 2, 2)
  (7,15,16) e=8 h=1: box (9, 1, 3)
  (7,15,17) e=8 h=2: box (9, 2, 2)
  (7,15,18) e=8 h=3: box (10, 3, 1)
  (7,16,17) e=9 h=1: box (10, 2, 2)
  (7,16,18) e=9 h=2: box (11, 1, 3)
  (8,11,12) e=3 h=1: box (7, 3, 1)
  (8,11,15) e=3 h=4: box (9, 2, 2)
  (8,13,14) e=5 h=1: box (7, 3, 2)
  (8,13,15) e=5 h=2: box (8, 2, 2)
  (8,13,17) e=5 h=4: box (10, 2, 2)
  (8,15,18) e=7 h=3: box (9, 3, 2)
  (8,15,19) e=7 h=4: box (11, 2, 2)
  (8,17,18) e=9 h=1: box (11, 1, 3)
  (8,17,19) e=9 h=2: box (10, 2, 2)
  (9,13,16) e=4 h=3: box (8, 3, 2)
  (9,13,20) e=4 h=7: box (9, 4, 1)
  (9,14,15) e=5 h=1: box (8, 2, 2)
  (9,14,16) e=5 h=2: box (9, 4, 1)
  (9,14,17) e=5 h=3: box (9, 2, 3)
  (9,14,20) e=5 h=6: box (9, 3, 2)
  (9,16,17) e=7 h=1: box (9, 4, 1)
  (9,16,19) e=7 h=3: box (10, 3, 2)
  (9,17,20) e=8 h=3: box (11, 2, 3)
  (9,19,20) e=10 h=1: box (11, 1, 4)
  (10,13,18) e=3 h=5: box (10, 3, 2)
  (10,13,21) e=3 h=8: box (9, 3, 2)
  (10,17,18) e=7 h=1: box (9, 3, 2)
  (10,17,19) e=7 h=2: box (9, 3, 2)
  (10,17,21) e=7 h=4: box (10, 2, 3)
  (11,14,18) e=3 h=4: box (9, 5, 1)
  (11,14,21) e=3 h=7: box (10, 3, 2)
  (11,15,16) e=4 h=1: box (7, 3, 2)
  (11,15,20) e=4 h=5: box (9, 4, 2)
  (11,16,18) e=5 h=2: box (8, 4, 2)
  (11,16,19) e=5 h=3: box (10, 5, 1)
  (11,16,20) e=5 h=4: box (9, 3, 2)
  (11,17,18) e=6 h=1: box (8, 2, 3)
  (11,18,19) e=7 h=1: box (9, 4, 3)
  (11,18,20) e=7 h=2: box (11, 5, 1)
  (11,18,21) e=7 h=3: box (10, 2, 3)
  (11,19,20) e=8 h=1: box (9, 4, 2)
  (11,20,21) e=9 h=1: box (11, 5, 1)
  (12,17,18) e=5 h=1: box (10, 5, 1)
  (12,17,20) e=5 h=3: box (10, 3, 2)
  (12,17,21) e=5 h=4: box (10, 2, 3)
  (12,17,23) e=5 h=6: box (12, 4, 2)
  (12,19,20) e=7 h=1: box (10, 3, 2)
  (12,19,21) e=7 h=2: box (11, 2, 3)
  (12,19,22) e=7 h=3: box (11, 3, 4)
  (12,19,23) e=7 h=4: box (11, 4, 2)
  (13,16,24) e=3 h=8: box (11, 2, 4)
  (13,17,20) e=4 h=3: box (9, 4, 2)
  (13,17,24) e=4 h=7: box (10, 4, 4)
  (13,18,19) e=5 h=1: box (9, 4, 2)
  (13,18,20) e=5 h=2: box (9, 3, 3)
  (13,18,22) e=5 h=4: box (11, 6, 1)
  (13,18,24) e=5 h=6: box (11, 3, 3)
  (13,19,24) e=6 h=5: box (10, 3, 3)
  (13,20,21) e=7 h=1: box (10, 2, 4)
  (13,20,22) e=7 h=2: box (10, 4, 2)
  (13,20,23) e=7 h=3: box (12, 6, 1)
  (13,20,24) e=7 h=4: box (11, 4, 2)
  (13,21,22) e=8 h=1: box (10, 4, 4)
  (13,21,24) e=8 h=3: box (11, 2, 4)
  (13,22,23) e=9 h=1: box (11, 3, 3)
  (13,22,24) e=9 h=2: box (13, 6, 1)
  (13,23,24) e=10 h=1: box (11, 4, 2)
  (14,17,24) e=3 h=7: box (12, 5, 2)
  (14,19,20) e=5 h=1: box (9, 3, 3)
  (14,19,21) e=5 h=2: box (12, 6, 1)
  (14,19,22) e=5 h=3: box (9, 5, 2)
  (14,19,25) e=5 h=6: box (10, 4, 2)
  (14,23,24) e=9 h=1: box (12, 3, 5)
  (14,23,25) e=9 h=2: box (11, 3, 4)
  (15,19,24) e=4 h=5: box (11, 2, 4)
  (15,22,24) e=7 h=2: box (11, 2, 4)
  (15,22,25) e=7 h=3: box (11, 4, 2)
  (15,22,26) e=7 h=4: box (13, 7, 1)
  (15,23,24) e=8 h=1: box (11, 2, 4)
  (15,23,26) e=8 h=3: box (12, 5, 4)
  (16,21,24) e=5 h=3: box (13, 7, 1)
  (16,21,25) e=5 h=4: box (10, 4, 3)
  (16,23,24) e=7 h=1: box (13, 7, 1)
  (16,23,26) e=7 h=3: box (11, 5, 2)
  (16,23,27) e=7 h=4: box (12, 3, 4)
  (16,25,26) e=9 h=1: box (10, 3, 4)
  (16,25,27) e=9 h=2: box (12, 2, 5)
  (17,21,28) e=4 h=7: box (11, 3, 4)
  (17,22,26) e=5 h=4: box (10, 6, 2)
  (17,22,28) e=5 h=6: box (13, 8, 1)
  (17,23,24) e=6 h=1: box (10, 3, 4)
  (17,24,25) e=7 h=1: box (10, 5, 2)
  (17,24,26) e=7 h=2: box (11, 4, 4)
  (17,24,28) e=7 h=4: box (11, 3, 4)
  (17,25,28) e=8 h=3: box (11, 6, 2)
  (17,26,27) e=9 h=1: box (11, 2, 5)
  (17,26,28) e=9 h=2: box (11, 4, 3)
  (17,27,28) e=10 h=1: box (12, 4, 3)
  (18,23,29) e=5 h=6: box (12, 4, 3)
  (18,25,26) e=7 h=1: box (10, 5, 3)
  (18,25,27) e=7 h=2: box (15, 8, 1)
  (18,25,28) e=7 h=3: box (11, 3, 4)
  (19,24,30) e=5 h=6: box (11, 5, 3)
  (19,25,30) e=6 h=5: box (11, 4, 3)
  (19,26,27) e=7 h=1: box (10, 4, 4)
  (19,26,28) e=7 h=2: box (11, 3, 4)
  (19,26,29) e=7 h=3: box (12, 3, 4)
  (19,26,30) e=7 h=4: box (12, 6, 2)
  (19,27,28) e=8 h=1: box (12, 6, 2)
  (19,28,30) e=9 h=2: box (13, 3, 5)
  (19,29,30) e=10 h=1: box (13, 2, 6)
  (20,27,28) e=7 h=1: box (11, 3, 4)
  (20,27,29) e=7 h=2: box (12, 6, 2)
  (20,27,30) e=7 h=3: box (16, 9, 1)
  (20,27,31) e=7 h=4: box (12, 5, 4)
  (20,29,30) e=9 h=1: box (16, 9, 1)
  (21,29,30) e=8 h=1: box (10, 5, 4)
  (21,29,32) e=8 h=3: box (12, 3, 5)
  (22,29,32) e=7 h=3: box (11, 5, 4)
  (22,29,33) e=7 h=4: box (17, 10, 1)
  (22,31,32) e=9 h=1: box (12, 5, 3)
  (22,31,33) e=9 h=2: box (18, 10, 1)
  (23,30,34) e=7 h=4: box (13, 4, 4)
  (23,31,32) e=8 h=1: box (11, 3, 5)
  (23,31,34) e=8 h=3: box (11, 6, 4)
  (23,32,33) e=9 h=1: box (13, 3, 5)
  (23,32,34) e=9 h=2: box (12, 4, 4)
  (23,33,34) e=10 h=1: box (13, 7, 2)
  (25,33,36) e=8 h=3: box (14, 8, 2)
  (25,34,35) e=9 h=1: box (13, 4, 4)
  (25,34,36) e=9 h=2: box (13, 3, 6)
  (26,35,36) e=9 h=1: box (13, 3, 6)
  (26,35,37) e=9 h=2: box (13, 6, 3)
  (27,37,38) e=10 h=1: box (14, 6, 3)
  (29,39,40) e=10 h=1: box (14, 3, 7)
  total: 158
TABLE B: a<=11, mu>=12 class bases (lambda-lift extends each; Y+Z<=a-1 enforced)
  class (a=4, ebar=1, h=1): base (4,17,18), box (13, 1, 1)
  class (a=5, ebar=1, h=1): base (5,16,17), box (10, 1, 2)
  class (a=5, ebar=1, h=2): base (5,16,18), box (11, 2, 1)
  class (a=5, ebar=2, h=2): base (5,17,19), box (12, 1, 2)
  class (a=5, ebar=3, h=1): base (5,18,19), box (11, 2, 1)
  class (a=5, ebar=3, h=3): base (5,18,21), box (13, 1, 2)
  class (a=5, ebar=4, h=3): base (5,14,17), box (10, 2, 1)
  class (a=6, ebar=1, h=1): base (6,19,20), box (13, 1, 2)
  class (a=6, ebar=1, h=2): base (6,19,21), box (14, 2, 1)
  class (a=6, ebar=1, h=3): base (6,19,22), box (14, 1, 2)
  class (a=6, ebar=5, h=3): base (6,17,20), box (13, 1, 2)
  class (a=6, ebar=5, h=4): base (6,17,21), box (13, 2, 1)
  class (a=7, ebar=1, h=1): base (7,22,23), box (13, 1, 3)
  class (a=7, ebar=1, h=2): base (7,22,24), box (13, 2, 2)
  class (a=7, ebar=1, h=3): base (7,22,25), box (14, 3, 1)
  class (a=7, ebar=1, h=4): base (7,15,19), box (11, 2, 2)
  class (a=7, ebar=2, h=1): base (7,23,24), box (14, 2, 2)
  class (a=7, ebar=2, h=2): base (7,23,25), box (15, 1, 3)
  class (a=7, ebar=2, h=4): base (7,16,20), box (11, 2, 2)
  class (a=7, ebar=3, h=2): base (7,17,19), box (11, 3, 1)
  class (a=7, ebar=3, h=3): base (7,17,20), box (12, 1, 3)
  class (a=7, ebar=3, h=5): base (7,17,22), box (12, 2, 2)
  class (a=7, ebar=4, h=1): base (7,18,19), box (11, 2, 2)
  class (a=7, ebar=4, h=2): base (7,18,20), box (11, 2, 2)
  class (a=7, ebar=4, h=4): base (7,18,22), box (13, 1, 3)
  class (a=7, ebar=4, h=5): base (7,18,23), box (12, 3, 1)
  class (a=7, ebar=5, h=1): base (7,19,20), box (11, 3, 1)
  class (a=7, ebar=5, h=3): base (7,19,22), box (12, 2, 2)
  class (a=7, ebar=5, h=5): base (7,19,24), box (14, 1, 3)
  class (a=7, ebar=6, h=3): base (7,20,23), box (13, 2, 2)
  class (a=7, ebar=6, h=4): base (7,20,24), box (13, 3, 1)
  class (a=7, ebar=6, h=5): base (7,20,25), box (13, 2, 2)
  class (a=8, ebar=1, h=1): base (8,25,26), box (16, 1, 3)
  class (a=8, ebar=1, h=2): base (8,25,27), box (14, 2, 2)
  class (a=8, ebar=1, h=3): base (8,17,20), box (12, 3, 1)
  class (a=8, ebar=1, h=4): base (8,17,21), box (12, 2, 2)
  class (a=8, ebar=1, h=5): base (8,17,22), box (11, 3, 2)
  class (a=8, ebar=3, h=1): base (8,19,20), box (12, 3, 1)
  class (a=8, ebar=3, h=3): base (8,19,22), box (14, 1, 3)
  class (a=8, ebar=3, h=4): base (8,19,23), box (14, 2, 2)
  class (a=8, ebar=3, h=6): base (8,19,25), box (12, 2, 2)
  class (a=8, ebar=5, h=1): base (8,21,22), box (11, 3, 2)
  class (a=8, ebar=5, h=2): base (8,21,23), box (12, 2, 2)
  class (a=8, ebar=5, h=4): base (8,21,25), box (15, 2, 2)
  class (a=8, ebar=5, h=5): base (8,21,26), box (16, 1, 3)
  class (a=8, ebar=7, h=3): base (8,23,26), box (13, 3, 2)
  class (a=8, ebar=7, h=4): base (8,23,27), box (16, 2, 2)
  class (a=8, ebar=7, h=5): base (8,15,20), box (11, 3, 1)
  class (a=8, ebar=7, h=6): base (8,15,21), box (10, 2, 2)
  class (a=9, ebar=1, h=1): base (9,28,29), box (16, 1, 4)
  class (a=9, ebar=1, h=2): base (9,19,21), box (12, 2, 2)
  class (a=9, ebar=1, h=3): base (9,19,22), box (12, 3, 2)
  class (a=9, ebar=1, h=4): base (9,19,23), box (12, 4, 1)
  class (a=9, ebar=1, h=5): base (9,19,24), box (13, 2, 2)
  class (a=9, ebar=1, h=6): base (9,19,25), box (12, 4, 2)
  class (a=9, ebar=2, h=1): base (9,20,21), box (12, 2, 2)
  class (a=9, ebar=2, h=2): base (9,20,22), box (13, 1, 4)
  class (a=9, ebar=2, h=3): base (9,20,23), box (13, 2, 3)
  class (a=9, ebar=2, h=4): base (9,20,24), box (13, 2, 2)
  class (a=9, ebar=2, h=6): base (9,20,26), box (13, 3, 2)
  class (a=9, ebar=4, h=2): base (9,22,24), box (13, 2, 2)
  class (a=9, ebar=4, h=3): base (9,22,25), box (13, 3, 2)
  class (a=9, ebar=4, h=4): base (9,22,26), box (15, 1, 4)
  class (a=9, ebar=4, h=6): base (9,22,28), box (13, 4, 2)
  class (a=9, ebar=4, h=7): base (9,22,29), box (14, 4, 1)
  class (a=9, ebar=5, h=1): base (9,23,24), box (13, 2, 2)
  class (a=9, ebar=5, h=2): base (9,23,25), box (14, 4, 1)
  class (a=9, ebar=5, h=3): base (9,23,26), box (14, 2, 3)
  class (a=9, ebar=5, h=5): base (9,23,28), box (16, 1, 4)
  class (a=9, ebar=5, h=6): base (9,23,29), box (14, 3, 2)
  class (a=9, ebar=5, h=7): base (9,14,21), box (10, 2, 2)
  class (a=9, ebar=7, h=1): base (9,25,26), box (14, 4, 1)
  class (a=9, ebar=7, h=3): base (9,25,28), box (15, 3, 2)
  class (a=9, ebar=7, h=5): base (9,16,21), box (11, 2, 2)
  class (a=9, ebar=7, h=6): base (9,16,22), box (10, 4, 2)
  class (a=9, ebar=8, h=3): base (9,26,29), box (16, 2, 3)
  class (a=9, ebar=8, h=4): base (9,17,21), box (11, 2, 2)
  class (a=9, ebar=8, h=5): base (9,17,22), box (11, 4, 1)
  class (a=9, ebar=8, h=6): base (9,17,23), box (11, 3, 2)
  class (a=9, ebar=8, h=7): base (9,17,24), box (12, 2, 2)
  class (a=10, ebar=1, h=1): base (10,21,22), box (13, 1, 4)
  class (a=10, ebar=1, h=2): base (10,21,23), box (11, 2, 3)
  class (a=10, ebar=1, h=3): base (10,21,24), box (11, 3, 2)
  class (a=10, ebar=1, h=4): base (10,21,25), box (14, 4, 1)
  class (a=10, ebar=1, h=5): base (10,21,26), box (14, 3, 2)
  class (a=10, ebar=1, h=6): base (10,21,27), box (13, 3, 2)
  class (a=10, ebar=1, h=7): base (10,21,28), box (14, 3, 3)
  class (a=10, ebar=3, h=1): base (10,23,24), box (12, 3, 3)
  class (a=10, ebar=3, h=2): base (10,23,25), box (15, 4, 1)
  class (a=10, ebar=3, h=3): base (10,23,26), box (16, 1, 4)
  class (a=10, ebar=3, h=5): base (10,23,28), box (16, 3, 2)
  class (a=10, ebar=3, h=6): base (10,23,29), box (14, 2, 3)
  class (a=10, ebar=3, h=8): base (10,23,31), box (14, 3, 2)
  class (a=10, ebar=7, h=1): base (10,27,28), box (14, 3, 2)
  class (a=10, ebar=7, h=2): base (10,27,29), box (14, 3, 2)
  class (a=10, ebar=7, h=4): base (10,27,31), box (15, 2, 3)
  class (a=10, ebar=7, h=5): base (10,17,22), box (12, 3, 2)
  class (a=10, ebar=7, h=8): base (10,17,25), box (12, 4, 1)
  class (a=10, ebar=9, h=3): base (10,19,22), box (11, 3, 3)
  class (a=10, ebar=9, h=4): base (10,19,23), box (11, 3, 2)
  class (a=10, ebar=9, h=5): base (10,19,24), box (13, 3, 2)
  class (a=10, ebar=9, h=6): base (10,19,25), box (13, 4, 1)
  class (a=10, ebar=9, h=7): base (10,19,26), box (11, 3, 2)
  class (a=10, ebar=9, h=8): base (10,19,27), box (12, 2, 3)
  class (a=11, ebar=1, h=1): base (11,23,24), box (13, 1, 5)
  class (a=11, ebar=1, h=2): base (11,23,25), box (12, 2, 3)
  class (a=11, ebar=1, h=3): base (11,23,26), box (12, 3, 2)
  class (a=11, ebar=1, h=4): base (11,23,27), box (13, 3, 4)
  class (a=11, ebar=1, h=5): base (11,23,28), box (14, 5, 1)
  class (a=11, ebar=1, h=6): base (11,23,29), box (14, 2, 4)
  class (a=11, ebar=1, h=7): base (11,23,30), box (13, 4, 2)
  class (a=11, ebar=1, h=8): base (11,23,31), box (14, 4, 3)
  class (a=11, ebar=2, h=1): base (11,24,25), box (12, 2, 4)
  class (a=11, ebar=2, h=2): base (11,24,26), box (15, 1, 5)
  class (a=11, ebar=2, h=3): base (11,24,27), box (12, 4, 2)
  class (a=11, ebar=2, h=4): base (11,24,28), box (13, 2, 3)
  class (a=11, ebar=2, h=5): base (11,24,29), box (13, 4, 3)
  class (a=11, ebar=2, h=6): base (11,24,30), box (13, 3, 2)
  class (a=11, ebar=2, h=8): base (11,24,32), box (15, 4, 2)
  class (a=11, ebar=3, h=1): base (11,25,26), box (12, 3, 4)
  class (a=11, ebar=3, h=2): base (11,25,27), box (12, 4, 3)
  class (a=11, ebar=3, h=3): base (11,25,28), box (16, 1, 5)
  class (a=11, ebar=3, h=4): base (11,25,29), box (15, 5, 1)
  class (a=11, ebar=3, h=6): base (11,25,31), box (14, 2, 3)
  class (a=11, ebar=3, h=7): base (11,25,32), box (15, 2, 4)
  class (a=11, ebar=3, h=9): base (11,14,23), box (9, 3, 2)
  class (a=11, ebar=4, h=1): base (11,26,27), box (12, 3, 2)
  class (a=11, ebar=4, h=2): base (11,26,28), box (13, 2, 4)
  class (a=11, ebar=4, h=4): base (11,26,30), box (17, 1, 5)
  class (a=11, ebar=4, h=5): base (11,26,31), box (14, 3, 4)
  class (a=11, ebar=4, h=6): base (11,26,32), box (14, 4, 2)
  class (a=11, ebar=4, h=8): base (11,15,23), box (10, 2, 3)
  class (a=11, ebar=4, h=9): base (11,15,24), box (10, 5, 1)
  class (a=11, ebar=5, h=2): base (11,27,29), box (13, 4, 2)
  class (a=11, ebar=5, h=3): base (11,27,30), box (16, 5, 1)
  class (a=11, ebar=5, h=4): base (11,27,31), box (14, 3, 2)
  class (a=11, ebar=5, h=5): base (11,27,32), box (18, 1, 5)
  class (a=11, ebar=5, h=7): base (11,16,23), box (10, 4, 3)
  class (a=11, ebar=5, h=8): base (11,16,24), box (11, 3, 2)
  class (a=11, ebar=5, h=9): base (11,16,25), box (11, 4, 2)
  class (a=11, ebar=6, h=1): base (11,28,29), box (13, 2, 3)
  class (a=11, ebar=6, h=2): base (11,28,30), box (14, 3, 4)
  class (a=11, ebar=6, h=3): base (11,28,31), box (14, 2, 4)
  class (a=11, ebar=6, h=4): base (11,28,32), box (15, 4, 3)
  class (a=11, ebar=6, h=7): base (11,17,24), box (10, 3, 2)
  class (a=11, ebar=6, h=8): base (11,17,25), box (11, 5, 1)
  class (a=11, ebar=6, h=9): base (11,17,26), box (11, 4, 2)
  class (a=11, ebar=7, h=1): base (11,29,30), box (14, 4, 3)
  class (a=11, ebar=7, h=2): base (11,29,31), box (17, 5, 1)
  class (a=11, ebar=7, h=3): base (11,29,32), box (15, 2, 3)
  class (a=11, ebar=7, h=5): base (11,18,23), box (10, 4, 2)
  class (a=11, ebar=7, h=6): base (11,18,24), box (11, 4, 2)
  class (a=11, ebar=7, h=9): base (11,18,27), box (13, 3, 2)
  class (a=11, ebar=8, h=1): base (11,30,31), box (14, 4, 2)
  class (a=11, ebar=8, h=2): base (11,30,32), box (15, 3, 2)
  class (a=11, ebar=8, h=4): base (11,19,23), box (11, 2, 4)
  class (a=11, ebar=8, h=5): base (11,19,24), box (11, 2, 3)
  class (a=11, ebar=8, h=7): base (11,19,26), box (12, 5, 1)
  class (a=11, ebar=8, h=9): base (11,19,28), box (12, 4, 3)
  class (a=11, ebar=9, h=1): base (11,31,32), box (17, 5, 1)
  class (a=11, ebar=9, h=3): base (11,20,23), box (11, 3, 4)
  class (a=11, ebar=9, h=5): base (11,20,25), box (11, 3, 2)
  class (a=11, ebar=9, h=6): base (11,20,26), box (12, 4, 3)
  class (a=11, ebar=9, h=7): base (11,20,27), box (12, 2, 3)
  class (a=11, ebar=9, h=8): base (11,20,28), box (12, 4, 2)
  class (a=11, ebar=10, h=3): base (11,21,24), box (11, 4, 3)
  class (a=11, ebar=10, h=4): base (11,21,25), box (11, 4, 2)
  class (a=11, ebar=10, h=5): base (11,21,26), box (12, 2, 4)
  class (a=11, ebar=10, h=6): base (11,21,27), box (13, 5, 1)
  class (a=11, ebar=10, h=7): base (11,21,28), box (13, 4, 2)
  class (a=11, ebar=10, h=8): base (11,21,29), box (12, 3, 2)
  class (a=11, ebar=10, h=9): base (11,21,30), box (13, 2, 3)
  total: 172
TABLE B-supplement: classes (a<=11, ebar=h) whose lambda=0 member is Lg; base at lambda=1
  class (a=4, ebar=1=h): base (4,17,18), box (13, 1, 1)
  class (a=5, ebar=1=h): base (5,16,17), box (10, 1, 2)
  class (a=5, ebar=2=h): base (5,17,19), box (12, 1, 2)
  class (a=5, ebar=3=h): base (5,18,21), box (13, 1, 2)
  class (a=6, ebar=1=h): base (6,19,20), box (13, 1, 2)
  class (a=7, ebar=1=h): base (7,22,23), box (13, 1, 3)
  class (a=7, ebar=2=h): base (7,23,25), box (15, 1, 3)
  class (a=7, ebar=3=h): base (7,17,20), box (12, 1, 3)
  class (a=7, ebar=4=h): base (7,18,22), box (13, 1, 3)
  class (a=7, ebar=5=h): base (7,19,24), box (14, 1, 3)
  class (a=8, ebar=1=h): base (8,25,26), box (16, 1, 3)
  class (a=8, ebar=3=h): base (8,19,22), box (14, 1, 3)
  class (a=8, ebar=5=h): base (8,21,26), box (16, 1, 3)
  class (a=9, ebar=1=h): base (9,28,29), box (16, 1, 4)
  class (a=9, ebar=2=h): base (9,20,22), box (13, 1, 4)
  class (a=9, ebar=4=h): base (9,22,26), box (15, 1, 4)
  class (a=9, ebar=5=h): base (9,23,28), box (16, 1, 4)
  class (a=9, ebar=7=h): base (9,25,32), box (18, 1, 4)
  class (a=10, ebar=1=h): base (10,21,22), box (13, 1, 4)
  class (a=10, ebar=3=h): base (10,23,26), box (16, 1, 4)
  class (a=10, ebar=7=h): base (10,27,34), box (20, 1, 4)
  class (a=11, ebar=1=h): base (11,23,24), box (13, 1, 5)
  class (a=11, ebar=2=h): base (11,24,26), box (15, 1, 5)
  class (a=11, ebar=3=h): base (11,25,28), box (16, 1, 5)
  class (a=11, ebar=4=h): base (11,26,30), box (17, 1, 5)
  class (a=11, ebar=5=h): base (11,27,32), box (18, 1, 5)
  class (a=11, ebar=6=h): base (11,28,34), box (19, 1, 5)
  class (a=11, ebar=7=h): base (11,29,36), box (20, 1, 5)
  class (a=11, ebar=8=h): base (11,30,38), box (21, 1, 5)
  class (a=11, ebar=9=h): base (11,31,40), box (22, 1, 5)
  total: 30
```

---



---
◀ [Appendix B — Certificate tables](appendix-B-tables.md) · **Next ▶** [Appendix D — Formal verification (Lean)](appendix-D-lean.md)
