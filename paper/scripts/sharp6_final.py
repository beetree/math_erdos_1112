#!/usr/bin/env python3
"""Constructive harness for the bounded subset-sum covering lemma (Erdos #1112 paper).

Covers every hard-core triple (a,b,M) with max(G) <= Mmax by the multiset that the
paper's CURRENT route designates -- the ordered case tree D / P / L / E / T / B of
Section 4 -- and verifies each witness exactly (integer arithmetic only):

    budget x+y+z <= M-1   and   subset sums contain >= M consecutive integers.

  D  a | M          : y = a-1 copies of b, x = q-1 copies of a, z = cdiv(x_eff-(q-1), q)
                      copies of M, x_eff = cdiv(M-1+(a-1)b, a)          [Lemma caseD]
  P  a | b+M (r>=3) : (x,y,z) = (r-1, cdiv(M-r,2), (M-r)//2)            [Lemma caseP]
  L  e = h = g      : (x,y,z) = ((a-2)//2 + 2g, 1, cdiv(a-2,2))         [Lemma caseL]
  E  a,mu >= 12     : eta-box (Y,Z) = (t-1, cdiv(a-t,t)), t = min(eta, a-eta)
                                                                        [Lemma etabox]
  T  mu <= 11       : the APPLICABLE variant of Construction T -- variant A when
                      g = 1, the base form when g >= 2, never the short merge; if
                      its budget exceeds M-1 the triple must be a row of the
                      canonical Table A (../data/table-A.csv), whose box certificate
                      is then verified                                  [Lemma T / T-tail]
  B  a <= 11, mu>=12: the triple's class (a, e mod a, h) must be a row of the
                      canonical Table B (../data/table-B.csv); the base's box is
                      lifted to the member and verified                 [lambda-lift]

No searches, perturbations, or fallback witnesses anywhere: every multiset is the
one designated by the corresponding lemma, or a canonical-table certificate.

Exit status: 0 only if every triple verifies AND (at Mmax = 120) the totals match
the paper's advertised counts (83,251 triples; the Table-A rows hit are exactly the
172 canonical rows). Any failure or count mismatch exits nonzero.

Usage: python3 sharp6_final.py [Mmax=120]
"""
import csv
import os
import sys
from collections import Counter
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))


def cdiv(n, d):
    """Exact ceiling division for integers, d > 0."""
    if d <= 0:
        raise ValueError("denominator must be positive")
    return -(-n // d)


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


def box_reps(a, b, M, Y, Z):
    """Minimal-height representative per residue class mod a in the box j<=Y, k<=Z."""
    reps = {}
    for j in range(Y + 1):
        for k in range(Z + 1):
            v = j * b + k * M
            r = v % a
            if r not in reps or v < reps[r]:
                reps[r] = v
    return reps


# ------------------------------------------------ designated constructions
def des_D(a, b, M):
    q = M // a
    xeff = cdiv(M - 1 + (a - 1) * b, a)
    z = max(0, cdiv(xeff - (q - 1), q))
    return (q - 1, a - 1, z)


def des_P(a, b, M):
    r = (b + M) // a
    return (r - 1, cdiv(M - r, 2), (M - r) // 2)


def des_L(a, g):
    return ((a - 2) // 2 + 2 * g, 1, cdiv(a - 2, 2))


def des_E(a, b, M):
    ebar, mubar = (b - a) % a, M % a
    eta = (mubar * pow(ebar, -1, a)) % a
    t = min(eta, a - eta)
    Z = cdiv(a - t, t)
    reps = box_reps(a, b, M, t - 1, Z)
    if len(reps) < a:
        return None
    S = max(reps.values())
    return (cdiv(M - 1 + S, a), t - 1, Z)


def des_T(a, e, h):
    """The applicable variant of Construction T: variant A (g=1) or base form (g>=2)."""
    mu = e + h
    g = gcd(e, mu)
    e1, m1 = e // g, mu // g
    C1 = (e1 - 1) * (m1 - 1)
    y = m1 - 1
    if g == 1:
        z = max(e1 - 1, cdiv(max(a, mu) - 1 + 2 * C1 - y * e1, m1))
        x = y + z + 1
    else:
        z = max(e1 - 1, cdiv(a + cdiv(mu - 1, g) + 2 * C1 - y * e1, m1))
        x = y + z + g
    return (x, y, z)


# ------------------------------------------------ canonical certificate data
def load_table_A():
    rows = {}
    with open(os.path.join(HERE, "..", "data", "table-A.csv")) as f:
        for r in csv.DictReader(f):
            rows[(int(r["a"]), int(r["b"]), int(r["M"]))] = (
                int(r["x"]), int(r["Y"]), int(r["Z"]))
    return rows


def load_table_B():
    rows = {}
    with open(os.path.join(HERE, "..", "data", "table-B.csv")) as f:
        for r in csv.DictReader(f):
            rows[(int(r["a"]), int(r["ebar"]), int(r["h"]))] = (
                int(r["base_a"]), int(r["base_b"]), int(r["base_M"]),
                int(r["x"]), int(r["Y"]), int(r["Z"]))
    return rows


def main():
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    TA, TB = load_table_A(), load_table_B()
    tot = 0
    tags = Counter()
    hitA = set()
    failures = []

    def fail(a, b, M, tag, ms, why):
        failures.append((a, b, M, tag, ms, why))

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
                if M % a == 0:
                    tag, ms = 'D', des_D(a, b, M)
                elif (b + M) % a == 0:
                    tag, ms = 'P', des_P(a, b, M)
                elif e == h:
                    tag, ms = 'L', des_L(a, e)
                elif a >= 12 and mu >= 12:
                    tag, ms = 'E', des_E(a, b, M)
                    if ms is None:
                        fail(a, b, M, tag, None, "eta-box residue coverage failed")
                        continue
                elif mu <= 11:
                    tag, ms = 'T', des_T(a, e, h)
                    if sum(ms) > M - 1:
                        # designated budget fails: must be a canonical Table-A row
                        if (a, b, M) not in TA:
                            fail(a, b, M, 'T', ms, "budget fails and not in Table A")
                            continue
                        tag, ms = 'T-table', TA[(a, b, M)]
                        x, Y, Z = ms
                        if Y + Z > a - 1 or len(box_reps(a, b, M, Y, Z)) < a:
                            fail(a, b, M, tag, ms, "Table-A box invalid")
                            continue
                        hitA.add((a, b, M))
                else:
                    tag = 'B'
                    key = (a, e % a, h)
                    if key not in TB:
                        fail(a, b, M, tag, None, f"class {key} missing from Table B")
                        continue
                    ba, bb, bM, _, Y, Z = TB[key]
                    if M < bM or (b - bb) % a != 0 or (M - bM) != (b - bb):
                        fail(a, b, M, tag, None, f"not on lift ladder of base {(ba, bb, bM)}")
                        continue
                    reps = box_reps(a, b, M, Y, Z)
                    if len(reps) < a:
                        fail(a, b, M, tag, None, "lifted box loses residue coverage")
                        continue
                    ms = (cdiv(M - 1 + max(reps.values()), a), Y, Z)
                x, y, z = ms
                if x + y + z > M - 1:
                    fail(a, b, M, tag, ms, f"budget {x+y+z} > M-1 = {M-1}")
                elif not cover_check(a, b, M, x, y, z):
                    fail(a, b, M, tag, ms, "does not cover M consecutive integers")
                else:
                    tags[tag] += 1

    print(f"hard core M<={Mmax}: {tot} triples")
    print("branch counts:", dict(sorted(tags.items())))
    print(f"Table-A rows used: {len(hitA)} (canonical table has {len(TA)})")
    print(f"DESIGNATED-BRANCH FAILURES (must be 0): {len(failures)}")
    for f in failures[:30]:
        print("   ", f)

    bad = bool(failures)
    if Mmax == 120:
        if tot != 83251:
            print(f"COUNT MISMATCH: {tot} hard-core triples, expected 83,251")
            bad = True
        if hitA != set(TA):
            print(f"TABLE MISMATCH: used {len(hitA)} Table-A rows, expected all "
                  f"{len(TA)} canonical rows (every row has M <= 40 <= 120)")
            bad = True
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
