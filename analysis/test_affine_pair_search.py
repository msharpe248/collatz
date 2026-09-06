import json
from pathlib import Path
import unittest

from affine_pair_search import search
from word_surgery import orbit


def first_kind(u, depth):
    for t in range(1, depth+1):
        x, j = orbit(3*u+2, t)
        y, k = orbit(27*u+20, t)
        if x == y and j == k+2:
            return 'merge'
        if y == 9*x+2 and j == k and x % 3 == 2:
            if (x-2)//3 < u and 3**j <= 2**t:
                return 'return'
    return 'unresolved'


class AffinePairTests(unittest.TestCase):
    def test_complete_small_census(self):
        for depth in range(1, 10):
            row = search(depth)['levels'][-1]
            counts = {'merge': 0, 'return': 0, 'unresolved': 0}
            for u in range(2**depth):
                counts[first_kind(u, depth)] += 1
            self.assertEqual(counts, {'merge': row['merge_covered'],
                                     'return': row['return_covered'], 'unresolved': row['unresolved']})

    def test_saved_certificates_replay_with_lifts(self):
        data = json.loads(Path(__file__).with_name('affine_pair_search_results.json').read_text())
        for c in data['certificates']:
            r, t = c['parameter'], c['depth']
            for Q in (0, 1, 7):
                u = r+2**t*Q
                x, j = orbit(3*u+2, t)
                y, k = orbit(27*u+20, t)
                self.assertEqual((j, k), (c['small_odds'], c['large_odds']))
                if c['kind'] == 'merge':
                    self.assertEqual(x, y)
                    self.assertEqual(j, k+2)
                else:
                    v = c['next_parameter']+3**j*Q
                    self.assertLess(v, u)
                    self.assertEqual((x, y), (3*v+2, 27*v+20))

    def test_first_return_family(self):
        data = search(12)
        returns = [c for c in data['certificates'] if c['kind'] == 'return']
        self.assertEqual(len(returns), 1)
        self.assertEqual((returns[0]['parameter'], returns[0]['next_parameter']), (2308, 45))


if __name__ == '__main__':
    unittest.main()
