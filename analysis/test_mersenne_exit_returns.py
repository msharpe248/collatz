import json
from pathlib import Path
import unittest

from mersenne_exit_returns import census, match, path
from mersenne_exit_search import signature
from source_witness_search import trajectory


class ExitReturnTests(unittest.TestCase):
    def test_small_exhaustive_census(self):
        depth, drop = 12, 4
        modulus = 2 ** (depth - 2)
        source = target = pairs = 0
        for r in range(1, modulus, 4):
            e = r + modulus
            upper = 3 ** e
            lower = 3 ** (e - drop)
            hits = []
            for c, b in ((1, -7), (3, -10)):
                a = trajectory(c * upper + b, depth)
                d = trajectory(c * lower + b, depth)
                t = next((t for t in range(depth + 1)
                          if a[t][0] == d[t][0] and d[t][1] == a[t][1] + drop), None)
                sa = path(pow(3, e, 2 ** depth), c, b, depth)
                sb = path(pow(3, e - drop, 2 ** depth), c, b, depth)
                self.assertEqual(t, match(sa, sb, drop))
                hits.append(t is not None)
            source += hits[0]
            target += hits[1]
            pairs += all(hits)
        result = census(depth, drop)
        self.assertEqual((source, target, pairs),
                         (result['source_return_residues'],
                          result['target_return_residues'], result['pair_return_residues']))

    def test_saved_rules_and_unresolved_premises(self):
        result = json.loads(Path(__file__).with_name('mersenne_exit_returns_results.json').read_text())
        depth = result['depth']
        modulus = 2 ** (depth - 2)
        rows = result['certificates']
        self.assertEqual(len(rows), 5)
        new = [r for r in rows if not r['direct_merge_within_bound']]
        self.assertEqual(len(new), 3)
        return_residues = {r['exponent_residue'] for r in rows}
        for rule in rows:
            e, d = rule['exponent_residue'], rule['drop']
            residue = pow(3, e - d, 2 ** depth)
            for Q in (1, 7, 2 ** 32):
                Y = residue + 2 ** depth * Q
                for c, b, t in ((1, -7, rule['source_depth']),
                                 (3, -10, rule['target_depth'])):
                    upper = trajectory(c * 3 ** d * Y + b, t)[-1]
                    lower = trajectory(c * Y + b, t)[-1]
                    self.assertEqual(upper[0], lower[0])
                    self.assertEqual(lower[1], upper[1] + d)
            if rule in new:
                self.assertIsNone(signature(residue, depth))
                self.assertNotIn((e - d) % modulus, return_residues)

    def test_invalid_bounds(self):
        for depth, drop in ((3, 4), (21, 4), (12, 0), (12, 6)):
            with self.assertRaises(ValueError):
                census(depth, drop)


if __name__ == '__main__':
    unittest.main()
