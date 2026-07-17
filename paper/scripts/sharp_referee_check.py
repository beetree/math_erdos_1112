#!/usr/bin/env python3
"""HOSTILE-REFEREE independent checker for the bounded subset-sum covering lemma
(Erdos #1112 paper). Written from scratch; deliberately does NOT import or mirror
sharp6_final.py.

For every hard-core triple M <= Mmax it takes the construction DESIGNATED BY THE
PAPER'S CURRENT ROUTE (the ordered case tree D/P/L/E/T/B of Section 4 -- exact
stated witnesses, no searches, no perturbations; Case T uses the applicable
variant of Construction T, variant A for g = 1 and the base form for g >= 2,
never the retired short merge), builds the multiset, computes exact subset sums
with integer arithmetic only, and checks:
    budget <= M-1   and   subset sums contain >= M consecutive integers.
Plus: brute-force checks of the machinery lemmas, L1/L2/L3, L4 + minimal-alphabet
enumeration (two independent methods), Table A/B certificate verification
(expecting the canonical 172 + 178 rows), the T-line scan to a = 3000 whose
failure set must equal Table A exactly (with the exact rational tail margin,
min 993 at a = 3000), the Case-P reach inequalities (E1)/(E2)/(F1)/(F2),
lambda-lift chains, the eta-box algebra scan, and random spot checks.

Exit status: 0 only if there are no FAILs and no WARNs.

Usage: python sharp_referee_check.py [Mmax=120]
"""
import sys, os, re, random
from fractions import Fraction
from math import gcd


def cdiv(n, d):
    """Exact ceiling division for integers, d > 0."""
    if d <= 0:
        raise ValueError("denominator must be positive")
    return -(-n // d)
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
    """Case D, a|M: the paper's DESIGNATED witness -- a-1 copies of b, q-1 copies
    of a, and z = cdiv(x_eff - (q-1), q) copies of M, x_eff = cdiv(M-1+(a-1)b, a).
    No optimization: exactly the multiset of the Case-D lemma."""
    q = M // a
    xeff = cdiv(M - 1 + (a - 1) * b, a)
    z = max(0, cdiv(xeff - (q - 1), q))
    return (q - 1, a - 1, z)

def des_P(a, b, M):           # Lemma caseP: the uniform pair-frame, all r >= 3
    r = (b + M) // a
    return (r - 1, cdiv(M - r, 2), (M - r) // 2)

def des_L(a, g):              # Lemma L: (floor((a-2)/2)+2g, 1, cdiv(a-2, 2))
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
    Z = cdiv(a - t, t)
    reps = box_reps(a, b, M, t - 1, Z)
    if len(reps) < a:
        return None
    S = max(reps.values())
    return (cdiv(M - 1 + S, a), t - 1, Z)

def T_construction(a, e, h):
    """Construction T, the APPLICABLE variant only: variant A (two-frame merge)
    when g = 1, the base form when g >= 2. The retired short merge is not used,
    matching the paper's merge-robust route and the Lean development."""
    mu = e + h
    g = gcd(e, mu)
    e1, m1 = e // g, mu // g
    C1 = (e1 - 1) * (m1 - 1)
    y = m1 - 1
    if g == 1:
        z = max(e1 - 1, cdiv(max(a, mu) - 1 + 2 * C1 - y * e1, m1))
        return (y + z + 1, y, z)                              # variant A, x = c+1
    z = max(e1 - 1, cdiv(a + cdiv(mu - 1, g) + 2 * C1 - y * e1, m1))
    return (y + z + g, y, z)                                  # base form, x = c+g

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
                    if (a, b, M) in A:
                        report("FAIL", f"table A duplicate row ({a},{b},{M})")
                    A[(a, b, M)] = (x, Y, Z)
            elif sec in ("B", "BS"):
                m = re.match(r"class \(a=(\d+), ebar=(\d+)(?:=h)?(?:, h=(\d+))?\): base \((\d+),(\d+),(\d+)\), box \((\d+), (\d+), (\d+)\)", line)
                if m:
                    a, ebar, h, ba, bb, bM, x, Y, Z = (int(v) if v else None for v in m.groups())
                    if h is None:
                        h = ebar
                    key = (a, ebar, h)
                    if key in B:
                        report("FAIL", f"table B duplicate class key {key}")
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
        return "P", des_P(a, b, M), ""
    if e == h:
        return "L", des_L(a, e), ""
    if a >= 12 and mu >= 12:
        ms = des_ETA(a, b, M)
        return "E", ms, "" if ms else "residue-coverage failed"
    if mu <= 11:
        ms = T_construction(a, e, h)
        if sum(ms) <= M - 1:
            return "T", ms, ""
        if (a, b, M) in TA:
            x, Y, Z = TA[(a, b, M)]
            return "T-table", (x, Y, Z), ""
        return "T", None, "budget fails and no Table A entry"
    # a <= 11, mu >= 12
    ebar = e % a
    key = (a, ebar, h)
    if key not in TB:
        return "B", None, f"class {key} missing from Table B"
    ba, bb, bM, bx, Y, Z = TB[key]
    if M < bM:
        return "B", None, f"member M={M} below class base M={bM} (lift only goes up)"
    if (b - bb) % a != 0 or (M - bM) != (b - bb):
        return "B", None, f"member not on class lift ladder from base {(ba,bb,bM)}"
    reps = box_reps(a, b, M, Y, Z)
    if len(reps) < a:
        return "B", None, "lifted box loses residue coverage (impossible if base ok)"
    S = max(reps.values())
    return "B", (cdiv(M - 1 + S, a), Y, Z), ""

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
        S = max(reps.values()); x = cdiv(L - 1 + S, nu)
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
                x = cdiv(M - 1 + S, a)
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
            x = cdiv(MM - 1 + S, a)
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
    for a in range(3, Mmax):
        for b in range(a + 1, Mmax):
            if gcd(a, b) != 1:
                continue
            for M in range(b + 1, min(a + b - 1, Mmax + 1)):
                if M - b > a - 2:
                    continue
                tot += 1
                tag, ms, note = designated(a, b, M, TA, TB)
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
    print(f"  hard-core triples: {tot} (paper claims 83,251 at Mmax=120)")
    print(f"  branch counts: {dict(sorted(tags.items()))}")
    if Mmax == 120:
        if tot != 83251:
            report("FAIL", f"hard-core count {tot} != claimed 83,251")
        expected = Counter({"D": 2392, "P": 2605, "L": 1420, "E": 71421,
                            "T": 3254, "T-table": 172, "B": 1987})
        if tags != expected:
            report("FAIL", f"branch counts {dict(tags)} != advertised {dict(expected)}")
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
        # entry must genuinely be an exception of the current route (else padding)
        if sum(T_construction(a, e, h)) <= M - 1:
            report("FAIL", f"Table A entry ({a},{b},{M}) is NOT a failure of Construction T")
    print(f"  Table A: {len(TA)} entries checked, invalid: {bad}")
    if len(TA) != 172:
        report("FAIL", f"Table A has {len(TA)} entries, canonical route expects 172")
    bad = 0
    for (a, ebar, h), (ba, bb, bM, x, Y, Z) in TB.items():
        e = bb - ba
        ok_ctx = ba == a and gcd(a, bb) == 1 and bM - bb == h and e % a == ebar and \
                 (bM - ba) >= 12 and bM % a != 0 and (bb + bM) % a != 0 and e != h
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
                    if (ba, bb, bM) != found:
                        report("FAIL", f"Table B base {(a,ebar,h)}=({ba},{bb},{bM}) != first branch-B member {found}")
    for m in missing:
        report("FAIL", f"Table B missing class {m[:3]} (first member {m[3]})")
    print(f"  Table B completeness: {len(missing)} missing classes")

def part_Tscan(TA):
    print("== PART 4: T-line scan (mu<=11, applicable variant) to a=3000 + exact tail ==")
    failures = set()
    margins = {}
    for e in range(1, 11):
        for h in range(1, 11):
            mu = e + h
            if mu > 11 or e == h:
                continue
            g = gcd(e, mu)
            e1, m1 = e // g, mu // g
            C1 = (e1 - 1) * (m1 - 1)
            for a in range(max(3, h + 2), 3001):
                if gcd(a, e) != 1 or mu % a == 0 or (2 * e + h) % a == 0:
                    continue
                M = a + mu
                if sum(T_construction(a, e, h)) > M - 1:
                    failures.add((a, a + e, M))
            # exact rational tail margin at a0 = 3000, using the paper's beta(a):
            # beta(a) = 2[(m1-1) + (a + mu + 2C' - (m1-1)e')/m1 + 1] + g, tau = a+mu-1
            a0 = 3000
            beta = 2 * (Fraction(m1 - 1) + Fraction(a0 + mu + 2 * C1 - (m1 - 1) * e1, m1) + 1) + g
            margins[(e, h)] = Fraction(a0 + mu - 1) - beta
            if margins[(e, h)] <= 0:
                report("FAIL", f"T-line ({e},{h}): tail margin not positive at a=3000")
    mx = max(a for a, _, _ in failures) if failures else 0
    print(f"  scan failures: {len(failures)}, max a = {mx} (canonical: 172, max 29)")
    if len(failures) != 172 or mx != 29:
        report("FAIL", f"T-scan found {len(failures)} exceptions (max a={mx}), canonical 172/29")
    if failures != set(TA):
        onlyS = sorted(failures - set(TA))
        onlyA = sorted(set(TA) - failures)
        report("FAIL", f"T-scan failure set != Table A (scan-only: {onlyS}; table-only: {onlyA})")
    mmin = min(margins.values())
    argmin = min(margins, key=margins.get)
    print(f"  min tail margin at a=3000 over lines: {mmin} (exact), at line {argmin}; "
          "budget slope <= 2/3 < 1, so every margin grows for a > 3000")
    # min over ALL lines evaluated at a=3000 (the paper's quantifier); over lines
    # with a=3000 itself a valid member the min is 2983/3, attained at (1,2)
    if mmin != 993:
        report("FAIL", f"tail margin minimum {mmin} != expected 993")

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
            x = cdiv(M - 1 + S, a)
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
    print("== PART 6: Case P uniform pair-frame -- witnesses and reach inequalities ==")
    # exact witness verification on EVERY P hard-core triple with a <= 50, M <= 250,
    # enumerated directly over (b, M) so no r-range can truncate the sweep
    # (all P-triples with M <= Mmax are also checked exactly in PART 2)
    n = bad = 0
    for a in range(3, 51):
        for M in range(a + 3, 251):
            for b in range(a + 1, M):
                if (b + M) % a != 0 or gcd(a, b) != 1 or not (1 <= M - b <= a - 2):
                    continue
                x, y, z = des_P(a, b, M)
                n += 1
                if x + y + z != M - 1 or not covers(a, b, M, x, y, z):
                    bad += 1
                    report("FAIL", f"uniform pair-frame fails at ({a},{b},{M})")
    print(f"  uniform witnesses, ALL P-triples with a<=50, M<=250: {n}, failures {bad}")
    # the four reach inequalities (E1),(E2),(F1),(F2), arithmetic, a <= 150
    n = bad = 0
    for a in range(3, 151):
        for r in range(3, 2 * a):
            for M in range(a + 2, r * a - a):
                b = r * a - M
                if not (a < b < M) or gcd(a, b) != 1 or not (1 <= M - b <= a - 2):
                    continue
                x, y, z = r - 1, cdiv(M - r, 2), (M - r) // 2
                pp, q = a // 2, (a - 1) // 2
                n += 1
                if not ((a - 1) * b + M - 1 <= a * (r * z + x)          # (E1)
                        and q * (b + M) + M - 1 <= a * (r * z + x)      # (E2)
                        and pp * (b + M) + M - 1 <= a * (r * y + x)     # (F1)
                        and a * M - 1 <= a * (r * y + x)):              # (F2)
                    bad += 1
                    report("FAIL", f"reach inequality fails at ({a},{b},{M})")
    print(f"  reach inequalities (E1)/(E2)/(F1)/(F2), all {n} instances with "
          f"a<=150 and 3<=r<2a: failures {bad}")

def part_eta_algebra():
    print("== PART 7: eta-box algebra (sigma bound + budget threshold), a <= 400 ==")
    bad = 0
    for a in range(12, 401):
        for t in range(2, a // 2 + 1):
            sig = t + cdiv(a - t, t)
            if 2 * sig > a + 4:
                bad += 1
                report("FAIL", f"sigma bound fails a={a} t={t}: sigma={sig} > (a+4)/2")
            # budget implication with worst member M = a+12, crude S bound:
            M = a + 12
            if sig * (M + a) > a * M + t:
                bad += 1
                report("FAIL", f"eta budget threshold fails a={a} t={t} (M=a+12)")
            if t * (cdiv(a - t, t) + 1) < a:
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
        ell = cdiv(M - 1 + (delta - 1) * a, delta) + 1
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
    print(f"loaded tables: A={len(TA)} entries, B={len(TB)} classes\n")
    if len(TA) != 172:
        report("FAIL", f"canonical Table A must have 172 rows, loaded {len(TA)}")
    if len(TB) != 178:
        report("FAIL", f"canonical Table B must have 178 classes, loaded {len(TB)}")
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
    sys.exit(1 if FAIL else (2 if WARN else 0))

if __name__ == "__main__":
    main()
