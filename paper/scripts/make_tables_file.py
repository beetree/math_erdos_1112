#!/usr/bin/env python3
"""Generate probes2/sharp_tables.txt (the input sharp_referee_check.py reads) from the
canonical certificate data in ../data/certificate-data.md.

Run this once before sharp_referee_check.py:

    python3 make_tables_file.py
    python3 sharp_referee_check.py 120
"""
import os
import re
from pathlib import Path

SRC = Path(__file__).resolve().parent.parent / "data" / "certificate-data.md"
OUT = Path(__file__).resolve().parent / "probes2" / "sharp_tables.txt"

blocks = re.findall(r"```\n(.*?)```", SRC.read_text(encoding="utf-8"), re.S)
A = [tuple(map(int, m.groups())) for m in
     re.finditer(r"\((\d+),(\d+),(\d+)\)\s*(?:→|->)\s*\((\d+),(\d+),(\d+)\)", blocks[0])]
B = [tuple(map(int, m.groups())) for m in
     re.finditer(r"\[(\d+);(\d+),(\d+)\]\s*\((\d+),(\d+),(\d+)\)\s*(?:→|->)\s*\((\d+),(\d+),(\d+)\)",
                 blocks[1])]

OUT.parent.mkdir(exist_ok=True)
with OUT.open("w", encoding="utf-8") as f:
    f.write("TABLE A\n")
    for (a, b, M, x, Y, Z) in A:
        f.write(f"({a},{b},{M}) e={b - a} h={M - b}: box ({x}, {Y}, {Z})\n")
    f.write("TABLE B\n")
    for (a, ebar, h, ba, bb, bM, x, Y, Z) in B:
        f.write(f"class (a={a}, ebar={ebar}, h={h}): base ({ba},{bb},{bM}), box ({x}, {Y}, {Z})\n")

print(f"wrote {OUT}: Table A {len(A)} rows, Table B {len(B)} classes")
