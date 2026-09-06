import unittest

from word_surgery import boundary_check, census, orbit


class WordSurgeryTests(unittest.TestCase):
    def test_census_matches_direct_orbits(self):
        for row in census(9):
            t = row['depth']
            minima = {}
            covered = nc_total = nc_covered = 0
            for n in range(2**t):
                key = orbit(n, t)
                smaller = key in minima
                minima.setdefault(key, n)
                nc = all(2**s <= 3**orbit(n, s)[1] for s in range(1, t+1))
                covered += smaller
                nc_total += nc
                nc_covered += nc and smaller
            self.assertEqual(row['covered'], covered)
            self.assertEqual(row['noncontracting_prefixes'], nc_total)
            self.assertEqual(row['covered_noncontracting_prefixes'], nc_covered)

    def test_noncontracting_example(self):
        self.assertEqual(orbit(15, 6), (20, 4))
        self.assertEqual(orbit(14, 6), (20, 4))
        self.assertTrue(all(2**s <= 3**orbit(15, s)[1] for s in range(7)))

    def test_boundary_certificate(self):
        self.assertEqual(boundary_check()['odd_count'], 41)


if __name__ == '__main__':
    unittest.main()
