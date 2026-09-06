import unittest
from mersenne_safe_descent import cutoff, probe, report
from source_witness_search import trajectory


class SafeDescentTests(unittest.TestCase):
    def test_maximal_cutoff(self):
        for u in range(1, 1000):
            b = cutoff(u)
            self.assertLessEqual(3**b, 36*u)
            self.assertGreater(3**(b+1), 36*u)
        with self.assertRaises(ValueError):
            cutoff(0)

    def test_independent_first_hits(self):
        for h in list(range(64)) + [487, 512]:
            row = probe(h)
            a = trajectory(729*81**h-10, row['exit_depth'])
            bound = 2**row['cutoff_exponent']
            self.assertTrue(all(x >= bound for x, _, _ in a[:-1]))
            self.assertLess(a[-1][0], bound)
            self.assertEqual(a[-1][1], row['odd_steps'])
            self.assertLessEqual(3**row['cutoff_exponent'], 36*(16*64**h-1))

    def test_census_and_limits(self):
        r = report()
        self.assertEqual((r['descents'], r['depth_limits']), (513, 0))
        worst = max(r['probes'], key=lambda row: row['exit_depth'])
        self.assertEqual((worst['h'], worst['exit_depth']), (487, 6268))
        self.assertEqual(probe(0, 0)['kind'], 'depth_limit')
        with self.assertRaises(ValueError):
            probe(-1)


if __name__ == '__main__':
    unittest.main()
