"""Independent arithmetic checks against direct Terras trajectories."""
import unittest
from fractions import Fraction
from itertools import product

from sturmian_prefix_power import affine_prefixes, best_margin, sturmian
from survivor_cylinders import quotient_interval, terras
from mahler_certificate_search import candidates


def orbit(n, length):
    values = [n]
    for _ in range(length):
        values.append(terras(values[-1]))
    return values


class CertificateTests(unittest.TestCase):
    def test_affine_correction_matches_actual_orbits(self):
        for n in range(1, 150):
            values = orbit(n, 40)
            J, D = affine_prefixes([x % 2 for x in values[:-1]])
            for t, value in enumerate(values):
                self.assertEqual((1 << t) * value, 3 ** J[t] * n + D[t])
        self.assertEqual(orbit(3, 1)[1], 5)
        self.assertGreater(5, Fraction(3 * 3, 2))  # old drift-only bound fails

    def test_certificates_do_not_exclude_nonperiodic_actual_tails(self):
        checked = 0
        for n in range(1, 200):
            values = orbit(n, 40)
            word = [x % 2 for x in values[:-1]]
            for height, s, period, _ in best_margin(word, 10, 14):
                self.assertTrue(n > height or values[s] == values[s + period])
                checked += 1
        self.assertGreater(checked, 100)

    def test_swap_identity(self):
        for length in range(2, 9):
            for word in product((0, 1), repeat=length):
                for i in range(length - 1):
                    if word[i:i + 2] == (0, 1):
                        swapped = word[:i] + (1, 0) + word[i + 2:]
                        _, d = affine_prefixes(word)
                        _, e = affine_prefixes(swapped)
                        self.assertEqual(d[-1] - e[-1], (1 << i) * 3 ** sum(word[i + 2:]))

    def test_survivor_intervals_match_enumeration(self):
        for depth in range(8):
            for height in (0, 1, 2, 31, 127, 200):
                for residue in range(1 << depth):
                    interval = quotient_interval(depth, residue, height)
                    actual = []
                    for q in range(height // (1 << depth) + 1):
                        n = residue + (1 << depth) * q
                        if 1 <= n <= height and min(orbit(n, depth)) >= n:
                            actual.append(q)
                    expected = [] if interval is None else list(range(interval[0], interval[1] + 1))
                    self.assertEqual(actual, expected, (depth, residue, height))

    def test_exact_mechanical_word_and_float_rejection(self):
        self.assertEqual(sturmian(Fraction(2, 3), Fraction(0), 6), [0, 1, 1, 0, 1, 1])
        with self.assertRaises(TypeError):
            sturmian(0.7, Fraction(0), 10)

    def test_mahler_search_replays_known_and_new_finite_candidates(self):
        results = list(candidates(length=3, max_degree=3, prefix_length=100))
        self.assertEqual(len(results), 2)
        new = next(r for r in results if r["one_image"] == [1, 0, 1])
        degree_two = next(c for c in new["pade_candidates"] if c["degree"] == 2)
        self.assertEqual(degree_two["p0"], [1, 0, 0])
        self.assertEqual(degree_two["p1"], [-1, 0, 1])
        self.assertEqual((degree_two["observed_order"], degree_two["leading_coefficient"]), (5, -1))
        self.assertGreater(degree_two["growth_left"], degree_two["growth_right"])


if __name__ == "__main__":
    unittest.main()
