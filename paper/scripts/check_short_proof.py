#!/usr/bin/env python3
"""Exact finite corroboration of the short paper's designated constructions.
No certificate tables are read and no witness search is performed.
This is a regression check, not a replacement for the uniform prose proofs.
"""
from collections import Counter
from math import gcd
from itertools import combinations
from functools import reduce
import argparse


def ceildiv(n, d):
    return -(-n // d)


def frame(a, b, M, Y, Z, L, U):
    x = ceildiv(M - 1 + U - L, a)
    assert x >= 0 and x + Y + Z <= M - 1, (a, b, M, x, Y, Z, L, U)
    residues = {(j*b+l*M) % a for j in range(Y+1) for l in range(Z+1)
                if L <= j*b+l*M <= U}
    assert len(residues) == a, (a, b, M, 'residues', L, U)
    return x, Y, Z


def path(a, b, M, reverse=False):
    p, q = (M, b) if reverse else (b, M)
    eta = q * pow(p, -1, a) % a
    t = min(eta, a-eta)
    Z, r = divmod(a-1, t)
    S = max((t-1)*p+(Z-1)*q, r*p+Z*q) if eta == t else (t-1)*p+Z*q
    Y, Z = (Z, t-1) if reverse else (t-1, Z)
    return frame(a, b, M, Y, Z, 0, S)


def witness(a, b, M):
    e, h = b-a, M-b
    if (b+M) % a == 0:
        r = (b+M)//a
        return 'movers', (r-1, ceildiv(M-r, 2), (M-r)//2)
    eta = M * pow(b, -1, a) % a
    t = min(eta, a-eta)
    K = t-1+(a-1)//t
    if a % 2:
        n = a//2
        if K <= n:
            return 'odd-generic', path(a, b, M)
        if eta == 2:
            if e == h and h in (1, 2):
                return f'odd-spacing-{h}', (n+2*h-1, 1, n)
            return 'odd-two', path(a, b, M)
        if eta == a-2:
            L, U = (b, b+(n-1)*M) if n >= 3 else (b, M+2*b)
            return 'odd-minus-two', frame(a, b, M, 2, n-1, L, U)
        assert eta in (n, n+1)
        return 'odd-middle', path(a, b, M, eta == n+1)
    n = a//2
    if K <= n-1:
        return 'even-generic', path(a, b, M)
    if a == 10:
        return 'even-ten', path(a, b, M, eta != 3)
    return 'even-edge', path(a, b, M)


def pair_target(p, h, N):
    s, r = divmod(N, h)
    assert gcd(p,h) == 1 and N >= 2*h
    return Counter({p: h-1, h: p+s-2+(r >= p)})


def scaled_interlace(C, d, q):
    result = Counter({d*v:c for v,c in C.items()})
    result[q] += d-1
    return result


def sharp(G):
    G = tuple(sorted(G))
    M = G[-1]
    H = G[:-1]
    d = reduce(gcd,H)
    e = H[-1]//d
    if len(H) >= 3:
        C = sharp(tuple(v//d for v in H))
        C[e] += ceildiv(M,e)-1
        return scaled_interlace(C,d,M)
    a,b = H
    if d > 1:
        return scaled_interlace(pair_target(a//d,b//d,M),d,M)
    if 2*b <= M:
        return pair_target(a,b,M)
    if a+b <= M+1:
        C = Counter({a:b-1,b:a-1})
        if a+b <= M:
            C[b] += 1
        return C
    for p,q in ((a,b),(b,a)):
        d = gcd(p,M)
        if d > 1:
            return scaled_interlace(pair_target(p//d,M//d,M),d,q)
    _, counts = witness(a,b,M)
    return Counter(dict(zip((a,b,M),counts)))


def verify_counter(M, counts):
    bits = 1
    for v, c in counts.items():
        assert c >= 0
        for _ in range(c):
            bits |= bits << v
    assert sum(counts.values()) <= M-1, (M, counts)
    run = bits
    length = 1
    while length*2 <= M:
        run &= run >> length
        length *= 2
    if length < M:
        run &= run >> (M-length)
    assert run, (M, counts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max', type=int, default=150)
    args = parser.parse_args()
    counts = Counter()
    for M in range(3, args.max+1):
        for a in range(3, M-1):
            for b in range(max(a+1, M+2-a), M):
                if gcd(a,b) != 1 or gcd(a,M) != 1 or gcd(b,M) != 1:
                    continue
                branch, ws = witness(a,b,M)
                verify_counter(M, dict(zip((a,b,M),ws)))
                counts[branch] += 1
    reduced = 0
    # Test the whole recursive funnel, including alphabets larger than triples.
    for size in range(3,15):
        for G in combinations(range(1,15),size):
            if reduce(gcd,G) != 1:
                continue
            C = sharp(G)
            assert set(C) <= set(G)
            verify_counter(max(G),C)
            reduced += 1
    for G in combinations(range(1,76),3):
        if reduce(gcd,G) != 1:
            continue
        C = sharp(G)
        assert set(C) <= set(G)
        verify_counter(max(G),C)
        reduced += 1
    assert counts
    print(f'Checked the full inductive construction on {reduced} alphabets.')
    print(f'Checked {sum(counts.values())} pairwise coprime dense triples through M={args.max}.')
    print(dict(sorted(counts.items())))
    print('All designated budgets, residue frames, and subset-sum runs passed.')


if __name__ == '__main__':
    main()
