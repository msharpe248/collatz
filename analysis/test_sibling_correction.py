from fractions import Fraction
import itertools
import unittest
from paradoxical_cylinders import step


def compress(x):
    return (x-1)//4 if x % 24 == 5 else x


def rank(x):
    residues = (1, 7, 11, 13, 17, 19, 23)
    return 7*(x//24)+residues.index(x % 24)


class SiblingCorrectionControls(unittest.TestCase):
    def test_comparison_ranks(self):
        seen = set()
        for x in range(7, 10000, 2):
            if x % 3 == 0:
                continue
            y = compress(x)
            self.assertLessEqual(y, x)
            self.assertGreater(y, 1)
            self.assertEqual(y % 2, 1)
            self.assertNotEqual(y % 3, 0)
            self.assertNotEqual(y % 24, 5)
            self.assertLessEqual(10*rank(y), 3*x)
            if x % 24 != 5:
                self.assertNotIn(rank(x), seen)
                seen.add(rank(x))
        self.assertEqual(compress(7), compress(29))  # pair-freeness is essential
        for r in range(1, 101):
            self.assertLessEqual((1+Fraction(1, 10*r))**10, Fraction(2*r+1, 2*r-1))

    def test_all_small_pair_free_sets(self):
        values = [x for x in range(7, 62, 2) if x % 3]
        for size in range(6):
            for selected in itertools.combinations(values, size):
                if any(4*x+1 in selected for x in selected):
                    continue
                compressed = [compress(x) for x in selected]
                self.assertEqual(len(set(compressed)), size)
                product = Fraction(1)
                for x in selected:
                    product *= 1+Fraction(1, 3*x)
                self.assertLessEqual(product**10, 2*size+1)

    def test_actual_eligible_prefixes(self):
        for seed in range(7, 501):
            if seed % 3 == 0:
                continue
            value, odd = seed, 0
            seen, odd_values = set(), set()
            for t in range(151):
                self.assertFalse(any(4*x+1 in odd_values for x in odd_values))
                self.assertLessEqual(((1 << t)*value)**10,
                                     (3**odd*seed)**10*(2*odd+1))
                if value <= 5 or value in seen:
                    break
                seen.add(value)
                if value % 2:
                    odd_values.add(value)
                    odd += 1
                value = step(value)


if __name__ == '__main__':
    unittest.main()
