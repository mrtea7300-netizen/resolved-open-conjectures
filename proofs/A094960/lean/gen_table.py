#!/usr/bin/env python3
"""Print the witness table `nonMemberTable` of Kellner/Bernoulli.lean.

For each k in 1..192 that is not one of the ten terms of A094960, the first (j, p) with
j >= 1, 2j + 1 <= k, p prime, (p - 1) | 2j and p not dividing k * C(k-1, 2j).
Lean re-checks every entry (theorem `table_ok`) and that the table covers all k (`cover_ok`).

Usage: python gen_table.py            (prints the Lean list)
       python gen_table.py --write    (replaces the list in Kellner/Bernoulli.lean)
"""
import os
import re
import sys
from math import comb

MEMBERS = [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]


def isprime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def table():
    out = []
    for k in range(1, 193):
        wit = None
        for j2 in range(2, k, 2):
            for p in range(2, j2 + 2):
                if isprime(p) and j2 % (p - 1) == 0 and (k * comb(k - 1, j2)) % p != 0:
                    wit = (k, j2 // 2, p)
                    break
            if wit:
                break
        if k in MEMBERS:
            assert wit is None, k
        else:
            assert wit is not None, k
            out.append(wit)
    return out


def fmt(tab):
    lines, line = [], "  ["
    for i, t in enumerate(tab):
        tok = "(%d, %d, %d)" % t + ("," if i + 1 < len(tab) else "]")
        if len(line) + len(tok) + 1 > 100:
            lines.append(line)
            line = "   " + tok
        else:
            line += ("" if line == "  [" else " ") + tok
    lines.append(line)
    return "\n".join(lines)


if __name__ == "__main__":
    text = fmt(table())
    if "--write" in sys.argv:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Kellner", "Bernoulli.lean")
        src = open(path, encoding="utf-8").read()
        pat = re.compile(r"(def nonMemberTable : List \(ℕ × ℕ × ℕ\) :=\n)(.*?)(\n\n)", re.S)
        assert pat.search(src)
        src = pat.sub(lambda m: m.group(1) + text + m.group(3), src, count=1)
        open(path, "w", encoding="utf-8", newline="\n").write(src)
        print("wrote", path)
    else:
        print(text)
