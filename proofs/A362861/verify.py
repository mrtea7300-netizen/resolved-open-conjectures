"""Standalone verification for OEIS A362861 Conjecture 1(i) and 1(ii) (first part)."""

from __future__ import annotations

EXPECTED_A362861 = [2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255]


def subset_bits(vals: list[int]) -> int:
    b = 1
    for v in vals:
        b |= b << v
    return b


def main() -> None:
    # 1. 5^a + 5^b (half-values)
    small5 = sorted({(5**a + 5**b) // 2 for a in range(4) for b in range(a + 1)})
    assert small5 == [1, 3, 5, 13, 15, 25, 63, 65, 75, 125]
    bits_small5 = subset_bits(small5)
    for e in EXPECTED_A362861:
        assert not ((bits_small5 >> e) & 1), f"Unexpected hit for {e}"

    base5 = sorted({(5**a + 5**b) // 2 for a in range(5) for b in range(a + 1)})
    bits5 = subset_bits(base5)
    missing5 = [n for n in range(1, 2088) if not ((bits5 >> n) & 1)]
    assert missing5 == EXPECTED_A362861
    B = 2087
    for b in range(5):
        x = (5**5 + 5**b) // 2
        assert x <= B - 255
        B += x
    assert B == 10290 and B - 255 == 10035 >= (5**6 + 625) // 2
    print(f"5^a + 5^b: exact 14 exceptions {EXPECTED_A362861}, covers [256..{B}] after t=5.")

    # 2. 3^a + 3^b (half-values)
    base3 = sorted({(3**a + 3**b) // 2 for a in range(3) for b in range(a + 1)})
    bits3 = subset_bits(base3)
    assert all((bits3 >> n) & 1 for n in range(1, 26))
    assert 25 >= (3**3 + 9) // 2
    print(f"3^a + 3^b: base {base3} covers [1..25], span 25 >= 18.")

    # 3. 3^a + 7^b (half-values)
    base37 = sorted({(3**a + 7**b) // 2 for a in range(4) for b in range(3)})
    bits37 = subset_bits(base37)
    assert all((bits37 >> n) & 1 for n in range(1, 169))
    assert 168 >= (3**4 + 49) // 2
    print(f"3^a + 7^b: base {base37} covers [1..168], span 168 >= 65.")

    print("ALL VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
