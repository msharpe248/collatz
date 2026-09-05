from fractions import Fraction
import itertools
import unittest
from paradoxical_cylinders import step


class ResidueCorrectionControls(unittest.TestCase):
    def test_rank_product_exact_arithmetic(self):
        for r in range(1, 101):
            self.assertLessEqual((1+Fraction(1, 9*r))**9, Fraction(2*r+1, 2*r-1))
        for size in range(7):
            for ranks in itertools.combinations(range(1, 10), size):
                product = Fraction(1)
                for r in ranks:
                    product *= Fraction(2*r+1, 2*r-1)
                self.assertLessEqual(product, 2*size+1)

    def test_actual_distinct_prefix_bound(self):
        checked = 0
        for seed in range(1, 501):
            if seed % 3 == 0:
                continue
            value, odd = seed, 0
            seen = set()
            for t in range(151):
                self.assertLessEqual(((1 << t)*value)**9,
                                     (3**odd*seed)**9*(2*odd+1))
                checked += 1
                if value == 1 or value in seen:
                    break
                seen.add(value)
                odd += value % 2
                value = step(value)
        self.assertGreater(checked, 1000)

    def test_eventual_residue_avoidance(self):
        for seed in range(1, 1025):
            value = seed
            for _ in range(seed.bit_length()+1):
                if value % 3:
                    break
                value = step(value)
            self.assertNotEqual(value % 3, 0)
            for _ in range(30):
                value = step(value)
                self.assertNotEqual(value % 3, 0)


if __name__ == '__main__':
    unittest.main()
