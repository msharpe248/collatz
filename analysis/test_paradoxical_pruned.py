import itertools
import unittest
from paradoxical_pruned import search, completion_possible
from paradoxical_cylinders import census, layers, orbit


def correction(word):
    value = 0
    for i, b in enumerate(word):
        value = 3*value+(1 << i) if b else value
    return value


class PruningControls(unittest.TestCase):
    def test_joint_congruence_against_direct_orbits(self):
        for length in range(9):
            modulus = 1 << length
            trajectories = [orbit(n, length) for n in range(2*modulus)]
            for word in itertools.product((0, 1), repeat=length):
                coefficient, corr = 3**sum(word), correction(word)
                for n, values in enumerate(trajectories):
                    realizes = tuple(x % 2 for x in values[:-1]) == word
                    compatible = (coefficient*n+corr) % modulus == 0
                    self.assertEqual(compatible, realizes)
                    joint = (n > 0 and coefficient < modulus and compatible
                             and (modulus-coefficient)*n <= corr)
                    direct = (realizes and n > 0 and values[-1] >= n
                              and coefficient < modulus)
                    self.assertEqual(joint, direct)

    def test_artificial_closing_correction(self):
        for depth, states in layers(7):
            modulus = 1 << depth
            for r, (endpoint, odd) in enumerate(states):
                q = max(0, (3-r+modulus-1)//modulus)
                seed = r+modulus*q
                value = endpoint+3**odd*q
                prefix_corr = modulus*value-3**odd*seed
                for extra in (0, 5):
                    length = depth+2*(odd+2*seed)+value+1+extra
                    k = 2*seed
                    d = (1 << (length-depth))*seed-3**k*value
                    self.assertGreaterEqual(d, 0)
                    self.assertLessEqual(k, length-depth)
                    self.assertLess(3**(odd+k), 1 << length)
                    self.assertLessEqual(d, (1 << (length-depth-k))*(3**k-(1 << k)))
                    self.assertEqual(3**(odd+k)*seed+3**k*prefix_corr+modulus*d,
                                     (1 << length)*seed)

    def test_all_short_suffix_envelopes(self):
        for length in range(9):
            for word in itertools.product((0, 1), repeat=length):
                for cut in range(length+1):
                    prefix, suffix = word[:cut], word[cut:]
                    k = sum(suffix)
                    upper = 3**k*correction(prefix)+(1 << (length-k))*(3**k-(1 << k))
                    self.assertLessEqual(correction(word), upper)

    def test_matches_exhaustive_search(self):
        expected = census(14)["segments"]
        actual = []
        for length in range(1, 15):
            row = search(length)
            self.assertEqual(row["status"], "complete")
            actual.extend(row["segments"])
        self.assertEqual(actual, expected)

    def test_fixed_prefix_envelopes_eventually_survive(self):
        for depth, states in layers(7):
            modulus = 1 << depth
            for r, (endpoint, odd) in enumerate(states):
                floor = r + modulus*max(0, (3-r+modulus-1)//modulus)
                corr = modulus*endpoint-3**odd*r
                threshold = depth+2*(odd+2*floor)+1
                for length in (threshold, threshold+7):
                    self.assertTrue(completion_possible(length, depth, r, odd, corr,
                                                        [3**j for j in range(length+1)]))

    def test_work_limit_cannot_claim_completeness(self):
        row = search(8, work_limit=1)
        self.assertEqual(row["status"], "incomplete_work_limit")
        self.assertGreater(row["pending_nodes"], 0)


if __name__ == "__main__":
    unittest.main()
