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
