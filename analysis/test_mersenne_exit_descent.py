import unittest
from mersenne_exit_descent import probe, report
from source_witness_search import trajectory


class ExitDescentTests(unittest.TestCase):
    def test_first_hits_and_exact_lower_bound(self):
        for h in range(64):
            row = probe(h)
            bound, initial = 16*64**h-1, 729*81**h-10
            d = row['depth']
            path = trajectory(initial, d)
            self.assertLess(path[-1][0], bound)
            self.assertTrue(all(x >= bound for x, _, _ in path[:-1]))
            self.assertEqual(path[-1][1], row['odd_steps'])
            minimum = row['necessary_minimum_depth']
            self.assertLess(initial, 2**minimum*bound)
            self.assertGreaterEqual(initial, 2**(minimum-1)*bound)
            self.assertGreaterEqual(d, minimum)

    def test_limits_are_not_failures(self):
        self.assertEqual(probe(0, 29)['kind'], 'depth_limit')
        self.assertEqual(probe(0, 30)['kind'], 'descent')
        self.assertEqual(probe(0, 0)['kind'], 'depth_limit')
        for h, cap in ((-1, 10), (0, -1)):
            with self.assertRaises(ValueError):
                probe(h, cap)

    def test_odd_run_transfer_parameter_exceeds_seed(self):
        self.assertEqual(trajectory(510, 11)[-1][0], 3*546+2)
        self.assertEqual(trajectory(511, 11)[-1][0], 27*546+20)
        self.assertGreater(546, 511)

    def test_census(self):
        result = report()
        self.assertEqual((result['descents'], result['depth_limits']), (513, 0))
        worst = max(result['probes'], key=lambda r: r['depth'])
        self.assertEqual((worst['h'], worst['depth']), (453, 1098))
        self.assertTrue(all(r['necessary_minimum_depth'] >= r['h']//3+6
                            for r in result['probes']))


if __name__ == '__main__':
    unittest.main()
