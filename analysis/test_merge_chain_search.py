from fractions import Fraction
import json
from pathlib import Path
import unittest

from merge_chain_search import RuleIndex, descend, single_rule_witness


ROOT = Path(__file__).resolve().parent
RULES = json.loads((ROOT/'merge_progressions_results.json').read_text())['rules']


def trace(n, t):
    counts, values = [0], [n]
    for _ in range(t):
        counts.append(counts[-1]+n % 2)
        n = (3*n+1)//2 if n % 2 else n//2
        values.append(n)
    return values, counts


class ChainTests(unittest.TestCase):
    def test_all_saved_certificates_by_direct_orbits(self):
        data = json.loads((ROOT/'merge_chain_search_results.json').read_text())
        self.assertEqual(len(data['certificates']), data['counts']['certificate'])
        for cert in data['certificates']:
            n, k = cert['seed'], cert['shift']
            values, counts = trace(n, k)
            self.assertTrue(all(2**i <= 3**j for i, j in enumerate(counts)))
            current = values[-1]
            D = Fraction(3**counts[-1], 2**k)
            self.assertEqual(str(D), cert['initial_deficit'])
            self.assertEqual(current, cert['shifted_seed'])
            for rule_id in cert['path']:
                r = RULES[rule_id]
                q, rem = divmod(current-r['seed'], r['seed_step'])
                self.assertEqual(rem, 0)
                self.assertGreaterEqual(q, 0)
                x = r['predecessor']+r['predecessor_step']*q
                self.assertTrue(0 < x < current)
                old_values, old_counts = trace(current, r['forward_time'])
                new_values, new_counts = trace(x, r['inverse_time'])
                self.assertEqual(old_values[-1], new_values[-1])
                self.assertTrue(all(2**i <= 3**j for i, j in enumerate(new_counts)))
                rho = Fraction(3**new_counts[-1]*2**r['forward_time'],
                               2**r['inverse_time']*3**old_counts[-1])
                self.assertEqual(rho, Fraction(r['seed_step'], r['predecessor_step']))
                self.assertGreaterEqual(rho, 1)
                D = max(Fraction(1), D/rho)
                current = x
            self.assertEqual(D, 1)
            self.assertEqual(current, cert['predecessor'])
            self.assertLess(current, n)

    def test_search_against_exhaustive_paths(self):
        ix = RuleIndex(RULES)

        def brute(n, D, threshold):
            return (n < threshold and D <= 1) or any(
                brute(x, max(Fraction(1), D/rho), threshold)
                for x, rho, _ in ix.edges(n))

        for n in range(1, 80):
            for D in (Fraction(1), Fraction(3, 2), Fraction(5, 2)):
                result = descend(ix, n, D, n)
                self.assertEqual(result['status'] == 'certificate', brute(n, D, n))

    def test_cap_and_single_rule_boundary(self):
        ix = RuleIndex(RULES)
        self.assertEqual(descend(ix, 767, Fraction(14348907, 8388608), 447,
                                 max_states=1)['status'], 'state_limit')
        self.assertFalse(single_rule_witness(ix, 447, 64))
        self.assertTrue(single_rule_witness(ix, 763, 64))

    def test_lifted_family_geometry(self):
        for Q in (0, 1, 7, 2**32):
            n = 447+549755813888*Q
            y, counts = trace(n, 23)
            self.assertEqual(y[-1], 767+940369969152*Q)
            self.assertEqual(counts[-1], 15)
            a, b, c = 511+626913312768*Q, 461+564859072962*Q, 307+376572715308*Q
            self.assertEqual(trace(a, 1)[0][-1], y[-1])
            self.assertEqual(trace(b, 1)[0][-1], trace(a, 17)[0][-1])
            self.assertEqual(trace(a, 17)[1][-1], 11)
            self.assertEqual(trace(c, 1)[0][-1], b)
            self.assertTrue(0 < c < n)


if __name__ == '__main__':
    unittest.main()
