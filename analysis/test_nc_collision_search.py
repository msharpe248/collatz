import unittest

from nc_collision_search import children, search
from word_surgery import orbit


class NCCollisionTests(unittest.TestCase):
    def test_layers_match_direct_orbits(self):
        rows = [(0, 0, 0)]
        for t in range(1, 11):
            rows = list(children(rows, t))
            expected = []
            for n in range(2**t):
                if all(2**i <= 3**orbit(n, i)[1] for i in range(t+1)):
                    e, j = orbit(n, t)
                    expected.append((n, j, e))
            self.assertEqual(sorted(rows), expected)

    def test_cap_is_not_reported_as_completion(self):
        result = search(10, 2)
        self.assertEqual(result['status'], 'state_limit')
        self.assertEqual(result['completed_depth'], 3)
        self.assertEqual(result['unsearched_next_depth'], 4)

    def test_different_counts_do_collide(self):
        self.assertEqual(orbit(31, 7), (182, 6))
        self.assertEqual(orbit(95, 7), (182, 5))
        for n in (31, 95):
            self.assertTrue(all(2**i <= 3**orbit(n, i)[1] for i in range(8)))


if __name__ == '__main__':
    unittest.main()
