"""Exact finite controls for the all-orbit packing/summability proof.
No finite trajectory is treated as evidence of an unbounded orbit.
"""
from collections import Counter
from fractions import Fraction
from math import comb
import unittest


def endpoint_and_ones(n, steps):
    ones = 0
    for _ in range(steps):
        bit = n % 2
        ones += bit
        n = (3*n+1)//2 if bit else n//2
    return n, ones


class OrbitPackingControls(unittest.TestCase):
    def test_full_residue_images(self):
        for m in range(4):
            k = 5*m
            records = [endpoint_and_ones(n, k) for n in range(32**m)]
            counts = Counter(j for _, j in records)
            self.assertEqual([counts[j] for j in range(k+1)], [comb(k, j) for j in range(k+1)])
            low = {end for end, j in records if j < 3*m}
            high_count = sum(j >= 3*m for _, j in records)
            self.assertTrue(all(end < 2*3**j for end, j in records))
            self.assertLessEqual(len(low), 2*27**m)
            self.assertLessEqual(8**m*high_count, 243**m)
            # One representative per endpoint is a maximal injective subset.
            image_count = len({end for end, _ in records})
            self.assertLessEqual(8**m*image_count, 2*216**m+243**m)

    def test_geometric_shell_majorant(self):
        for m in range(101):
            budget = 54*Fraction(27, 32)**m + Fraction(243, 8)*Fraction(243, 256)**m
            self.assertEqual(budget*8**(m+1)*32**m, 2*216**(m+1)+243**(m+1))
        total = 54/(1-Fraction(27, 32)) + Fraction(243, 8)/(1-Fraction(243, 256))
        self.assertLess(total, 1000)
        self.assertLess(2*Fraction(27, 32)**20+Fraction(243, 256)**20, 1)

    def test_coalescence_and_time_multiplicity_matter(self):
        self.assertEqual(endpoint_and_ones(1, 2)[0], endpoint_and_ones(4, 2)[0])
        # Distinct values in the trivial cycle stay distinct, but time repeats:
        # the orbit set has a finite reciprocal sum; its infinite time series does not.
        self.assertEqual(endpoint_and_ones(1, 2)[0], 1)
        self.assertEqual(endpoint_and_ones(2, 2)[0], 2)
        self.assertEqual(sum((Fraction(1, 1 if t % 2 == 0 else 2) for t in range(20))), 15)


if __name__ == '__main__':
    unittest.main()
