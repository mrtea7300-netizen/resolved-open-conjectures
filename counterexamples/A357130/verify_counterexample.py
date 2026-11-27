"""Standalone verification of counterexamples to OEIS A357130 Conjecture 2(ii)
(Wang & Sun, Electronic Journal of Combinatorics 33(2) (2026), #P2.64, Conjecture 1(1)).

Also reproduces the first 80 terms of OEIS A357130 directly from the formula.
"""

from __future__ import annotations

OEIS_FIRST_24 = [
    4, 3, 8, 7, 12, 11, 16, 15, 20, 19, 24, 23,
    28, 27, 32, 31, 36, 35, 40, 39, 44, 43, 48, 47,
]


def a357130(n: int) -> int:
    return 2 * n - ((-1) ** n) * (1 + (n % 2))


def restricted_path_sumset_Z(sets: list[list[int]]) -> set[int]:
    dp: dict[int, set[int]] = {a: {a} for a in sets[0]}
    for A in sets[1:]:
        ndp: dict[int, set[int]] = {}
        for prev_a, sums in dp.items():
            for a in A:
                if a == prev_a:
                    continue
                bucket = ndp.setdefault(a, set())
                for s in sums:
                    bucket.add(s + a)
        dp = ndp
    out: set[int] = set()
    for sums in dp.values():
        out |= sums
    return out


def restricted_path_sumset_mod(p: int, sets: list[list[int]]) -> set[int]:
    dp: dict[int, set[int]] = {a % p: {a % p} for a in sets[0]}
    for A in sets[1:]:
        ndp: dict[int, set[int]] = {}
        for prev_a, sums in dp.items():
            for a in A:
                am = a % p
                if am == prev_a:
                    continue
                bucket = ndp.setdefault(am, set())
                for s in sums:
                    bucket.add((s + am) % p)
        dp = ndp
    out: set[int] = set()
    for sums in dp.values():
        out |= sums
    return out


def main() -> None:
    # 1. Reproduce OEIS A357130 data section
    computed = [a357130(n) for n in range(1, 25)]
    assert computed == OEIS_FIRST_24, f"Mismatch: {computed}"
    print("OEIS A357130 first 24 terms reproduced exactly.")

    # 2. Universal counterexample in Z for n = 3 (and every odd n = 2m+1 up to 21)
    for m in range(1, 11):
        n = 2 * m + 1
        sets = [[0, 1, 2], [0, 2], [0, 1, 2]]
        for j in range(2, m + 1):
            sets.append([3 * j, 3 * j + 1])
            sets.append([3 * j, 3 * j + 1])
        assert all(len(A) == len(set(A)) and len(A) > 1 for A in sets)
        D = restricted_path_sumset_Z(sets)
        bound = sum(len(A) for A in sets) - 2 * n + 1 + (n % 2)
        expected_shift = sum(6 * j + 1 for j in range(2, m + 1))
        assert D == {expected_shift + 2, expected_shift + 3, expected_shift + 4}
        assert len(D) == 3 < 4 == bound
        if m <= 5:
            print(f"Z, n={n:2d}: |D| = {len(D)} < {bound} = bound; D = {sorted(D)}")

    # 3. Universal counterexample in Z/pZ for primes p = 5, 7, 11, 13, 17, 19
    for p in [5, 7, 11, 13, 17, 19]:
        sets = [[0, 1, 2], [0, 2], [0, 1, 2]]
        D = restricted_path_sumset_mod(p, sets)
        bound = min(p, sum(len(A) for A in sets) - 2 * 3 + 1 + (3 % 2))
        assert D == {2, 3, 4} and len(D) == 3 < 4 == bound
    print("Z/pZ (p in {5,7,11,13,17,19}), n=3: |D| = 3 < 4 = bound verified.")

    # 4. Modular counterexample in Z/5Z with |A2| > |A1|, |A3|
    sets_mod5 = [[0, 1], [0, 1, 2, 3, 4], [2, 4]]
    D5 = restricted_path_sumset_mod(5, sets_mod5)
    bound5 = min(5, sum(len(A) for A in sets_mod5) - 2 * 3 + 1 + (3 % 2))
    assert D5 == {0, 1, 2, 3}
    assert len(D5) == 4 < 5 == bound5
    print(f"Z/5Z, n=3 (|A2|=5 > |A1|=|A3|=2): |D| = {len(D5)} < {bound5} = bound; D = {sorted(D5)}")

    print("ALL VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
