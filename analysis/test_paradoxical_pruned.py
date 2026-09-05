import itertools
import unittest
from paradoxical_pruned import search, completion_possible
from paradoxical_cylinders import census, layers


def correction(word):
    value = 0
    for i, b in enumerate(word):
        value = 3*value+(1 << i) if b else value
    return value


class PruningControls(unittest.TestCase):
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
