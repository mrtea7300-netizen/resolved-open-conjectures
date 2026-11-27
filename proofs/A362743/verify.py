"""Standalone verification for OEIS A362743 Conjecture 1 (first part):
every positive integer n not in {1, 3, 4, 10, 12, 18} is a sum of distinct
numbers of the form 4^a + 5^b (a, b >= 0), and none of those 6 are.
"""

from __future__ import annotations

EXPECTED_EXCEPTIONS = [1, 3, 4, 10, 12, 18]


def main() -> None:
    # 1. All elements of {4^a + 5^b} <= 18
    small = sorted({4**a + 5**b for a in range(5) for b in range(5) if 4**a + 5**b <= 18})
    assert small == [2, 5, 6, 9, 17]

    # 2. Base 9 elements (a <= 2, b <= 2)
    base9 = sorted({4**a + 5**b for a in range(3) for b in range(3)})
    assert base9 == [2, 5, 6, 9, 17, 21, 26, 29, 41]

    # Exact subset sums of base9
    bits = 1
    for x in base9:
        bits |= bits << x
    missing_1_to_137 = [n for n in range(1, 138) if not ((bits >> n) & 1)]
    assert missing_1_to_137 == EXPECTED_EXCEPTIONS
    print(f"Base 9 elements {base9}: exact exceptions in [1..137] = {missing_1_to_137}")

    # 3. Extend by block t = 3: 65, 69, 89, 189
    B = 137
    for b in range(4):
        x = 4**3 + 5**b
        assert x <= B - 18, f"Gap at 4^3 + 5^{b} = {x} > {B - 18}"
        B += x
    assert B == 549 and (B - 18) == 531 >= 4**4 + 125
    print(f"After block t=3: covers [19..{B}], span = {B - 18} >= 4^4 + 125 = {4**4 + 125}")
    print("Inductive step for all t >= 4: adding 4^t+{1,5,25,125} adds 4^(t+1)+156 > 4^(t+1)+125.")
    print("ALL VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
