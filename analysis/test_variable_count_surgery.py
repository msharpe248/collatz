import unittest

from variable_count_surgery import canonical_levels, compare_counts
from word_surgery import orbit


class VariableCountTests(unittest.TestCase):
    def test_complete_canonical_rows(self):
        for t, rows in canonical_levels(9):
            self.assertEqual(sorted(r for r, _, _, _ in rows), list(range(2**t)))
            for r, j, e, nc in rows:
                self.assertEqual(orbit(r, t), (e, j))
                self.assertEqual(nc, all(2**s <= 3**orbit(r, s)[1]
                                         for s in range(t+1)))

    def test_quotient_formulas_against_lifted_orbits(self):
        # Check all pairs at small depths, including cases that do add coverage
        # outside the noncontracting survivor restriction.
        for t, rows in canonical_levels(6):
            L = 2**t
            for r, j, e, _ in rows:
                for s, k, f, _ in rows:
                    if k > j and f % 3**j == e:
                        q0 = (f-e) // 3**j
                        for Q in (1, 2):
                            n = r + L * (q0 + 3**(k-j)*Q)
                            x = s + L*Q
                            self.assertTrue(0 < x < n)
                            self.assertEqual(orbit(n, t)[0], orbit(x, t)[0])
                    if k < j:
                        for q in (0, 1, 2):
                            n = r + L*q
                            y = e + 3**j*q
                            if y % 3**k != f:
                                continue
                            x = s + L*(y // 3**k)
                            self.assertEqual(orbit(n, t)[0], orbit(x, t)[0])
                            if x < n:
                                self.assertEqual(q, 0)
                                self.assertEqual(e, f)

    def test_reported_small_depth_comparison(self):
        for row in compare_counts(9):
            self.assertEqual(row['added_by_lower_count_at_quotient_zero'], 0)
            self.assertEqual(row['added_by_higher_count_for_some_lifts'], 0)


if __name__ == '__main__':
    unittest.main()
