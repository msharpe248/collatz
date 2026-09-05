"""Independent finite controls for residue enumeration and interval endpoints."""
import unittest
from paradoxical_cylinders import layers, orbit, quotient_interval, census


class ParadoxicalControls(unittest.TestCase):
    def test_every_residue_matches_direct_iteration(self):
        for depth, states in layers(10):
            self.assertEqual(len(states), 1 << depth)
            for r, (endpoint, odd) in enumerate(states):
                values = orbit(r, depth)
                self.assertEqual(endpoint, values[-1])
                self.assertEqual(odd, sum(n % 2 for n in values[:-1]))

    def test_intervals_match_direct_seeds_and_boundaries(self):
        for depth, states in layers(8):
            for r, (endpoint, odd) in enumerate(states):
                interval = quotient_interval(depth, r, endpoint, odd)
                candidates = set(range(12))
                if interval:
                    lo, hi = interval
                    candidates.update((lo, hi, hi+1, max(0, lo-1)))
                for q in candidates:
                    n = r + (1 << depth)*q
                    values = orbit(n, depth)
                    direct = n >= 3 and values[-1] >= n and 3**sum(x%2 for x in values[:-1]) < 1 << depth
                    actual = interval is not None and interval[0] <= q <= interval[1]
                    self.assertEqual(actual, direct, (depth, r, q))

    def test_paper_example_and_no_truncated_subtraction(self):
        rows = census(8)["segments"]
        self.assertIn({"length": 8, "seed": 7, "endpoint": 8, "odd_steps": 5,
                       "quotient": 0, "first_descent_within_segment": 7}, rows)
        self.assertIsNone(quotient_interval(1, 0, 0, 0))
        self.assertIsNone(quotient_interval(2, 2, 1, 0, minimum=1))


if __name__ == "__main__":
    unittest.main()
