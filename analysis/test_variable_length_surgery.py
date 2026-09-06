import unittest

from variable_length_surgery import scan
from word_surgery import orbit


class VariableLengthTests(unittest.TestCase):
    def test_small_search_against_all_smaller_seeds(self):
        d = 8
        paths = {n: [orbit(n, t) for t in range(d+1)] for n in range(1, 2**d)}
        expected = dict(noncontracting_prefixes=0, equal_count_covered=0,
                        variable_length_additions=0, additions_preserving_noncontraction=0,
                        no_bounded_certificate=0)
        for n, pn in paths.items():
            if not all(2**t <= 3**j for t, (_, j) in enumerate(pn)):
                continue
            expected['noncontracting_prefixes'] += 1
            if any(paths[x][d] == pn[d] for x in range(1, n)):
                expected['equal_count_covered'] += 1
                continue
            general = strong = False
            for x in range(1, n):
                px = paths[x]
                for t, (y, j) in enumerate(pn):
                    for s, (z, k) in enumerate(px):
                        if y != z:
                            continue
                        general = True
                        strong |= (all(2**i <= 3**px[i][1] for i in range(s+1))
                                   and 2**s*3**j <= 2**t*3**k)
            expected['variable_length_additions'] += general
            expected['additions_preserving_noncontraction'] += strong
            expected['no_bounded_certificate'] += not general
        actual = scan(d)['counts']
        for key, val in expected.items():
            self.assertEqual(actual[key], val, key)

    def test_infinite_family_samples(self):
        for Q in (0, 1, 10, 100, 2**32):
            n, x = 111+4374*Q, 103+4096*Q
            self.assertTrue(0 < x < n)
            self.assertEqual(orbit(n, 1), (167+6561*Q, 1))
            self.assertEqual(orbit(x, 12), (167+6561*Q, 8))
            self.assertTrue(all(2**i <= 3**orbit(x, i)[1] for i in range(13)))
            self.assertLessEqual(2**12*3, 2*3**8)


if __name__ == '__main__':
    unittest.main()
