import json
from pathlib import Path
import unittest

from affine_bridge_search import classify_pair, search, step
from word_surgery import orbit


def replay(c, Q):
    """Replay actual integer paths, checking every recursive parameter."""
    t, u = c['depth'], c['parameter']
    original = u+2**t*Q
    x = 3*original+2
    clock = 0
    for bridge in c['bridges']:
        s = bridge['time']
        x, _ = orbit(x, s-clock)
        v = bridge['parameter']+3**bridge['exponent']*2**(t-s)*Q
        assert x == 3*v+2
        assert 0 <= v < original
        x = 27*v+20
        clock = s
    x, _ = orbit(x, t-clock)
    y, _ = orbit(27*original+20, t)
    assert x == y == c['endpoint']+3**c['exponent']*Q


class BridgeTests(unittest.TestCase):
    def test_saved_certificates(self):
        data = json.loads(Path(__file__).with_name('affine_bridge_search_results.json').read_text())
        for row in data['rows']:
            c = row['expanded']
            if c['kind'] == 'certificate':
                for Q in (0, 1, 7, 2**32):
                    replay(c, Q)

    def test_terminal_classification_remains_excluded(self):
        for u in range(1001):
            c = classify_pair(u)
            if c['kind'] == 'terminal_without_certificate':
                x, j = orbit(3*u+2, c['time'])
                y, k = orbit(27*u+20, c['time'])
                self.assertIn(x, (1, 2))
                self.assertIn(y, (1, 2))
                for _ in range(8):
                    self.assertFalse(x == y and j == k+2)
                    self.assertNotEqual(y, 9*x+2)
                    j, k = j+x % 2, k+y % 2
                    x, y = step(x), step(y)

    def test_bridge_28_and_explicit_limits(self):
        c = search(28, 12)
        self.assertEqual(c['bridges'], [dict(time=2, parameter=21, exponent=1)])
        self.assertEqual(classify_pair(28)['kind'], 'terminal_without_certificate')
        self.assertEqual(search(28, 12, max_bridges=0)['kind'], 'depth_limit')
        self.assertEqual(search(28, 12, state_cap=1)['kind'], 'state_cap')
        self.assertEqual(classify_pair(28, cap=1)['kind'], 'cap')

    def test_same_clock_multiple_bridges(self):
        # Independent brute-force paths, without deduplication, check the
        # closure implementation and earliest success on a complete sample.
        def brute(u, depth, budget):
            states = [(3*u+2, 1, 0)]
            y, q = 27*u+20, 3
            for t in range(depth+1):
                for x, p, used in states:
                    if (used < budget and x % 3 == 2 and (x-2)//3 < u
                            and 3**(p-1) <= 2**t):
                        states.append((9*x+2, p+2, used+1))
                if any((x,p)==(y,q) for x,p,_ in states):
                    return t
                states = [(step(x),p+x % 2,b) for x,p,b in states]
                q, y = q+y % 2, step(y)
            return None
        for u in range(100):
            c = search(u, 16)
            self.assertEqual(c['depth'] if c['kind']=='certificate' else None,
                             brute(u, 16, 2))


if __name__ == '__main__':
    unittest.main()
