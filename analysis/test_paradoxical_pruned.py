import itertools
import json
from pathlib import Path
import unittest
from paradoxical_pruned import search, completion_possible, advance
from paradoxical_cylinders import census, layers, orbit


def correction(word):
    value = 0
    for i, b in enumerate(word):
        value = 3*value+(1 << i) if b else value
    return value


class PruningControls(unittest.TestCase):
    def test_recorded_65_matches_independent_small_scan(self):
        # This independently checks the witnesses and the small-seed slice.
        # Absence above this finite range still relies on the pruned traversal.
        data = json.loads(Path(__file__).with_name("paradoxical_pruned_results.json").read_text())
        result = next(row for row in data["results"] if row["length"] == 65)
        self.assertEqual(result["status"], "complete")
        expected = []
        for seed in range(3, 65536):
            n, odd = seed, 0
            for _ in range(65):
                if n % 2:
                    n = (3*n+1)//2
                    odd += 1
                else:
                    n //= 2
            if n >= seed and 3**odd < 2**65:
                expected.append(seed)
        recorded = [row["seed"] for row in result["segments"]]
        self.assertEqual(recorded, expected)
        self.assertEqual(len(recorded), 244)
        self.assertTrue(all(row["first_descent_within_segment"] is not None
                            for row in result["segments"]))

    def test_jump_composition_matches_direct_iteration(self):
        for n in list(range(2048))+[2**80+17, 3**80+1]:
            for length in (0, 1, 7, 8, 9, 16, 27, 65):
                values = orbit(n, length)
                self.assertEqual(advance(n, length),
                                 (values[-1], sum(x % 2 for x in values[:-1])))

    def test_maximal_count_matches_all_count_oracle(self):
        for depth, states in layers(7):
            modulus = 1 << depth
            for r, (endpoint, odd) in enumerate(states):
                minimum = r+modulus*max(0, (3-r+modulus-1)//modulus)
                corr = modulus*endpoint-3**odd*r
                for length in (depth, depth+3, 27, 65):
                    powers = [3**j for j in range(length+1)]
                    possible = any(
                        powers[odd+k] < 1 << length and
                        powers[k]*corr+(1 << (length-k))*(powers[k]-(1 << k))
                        >= ((1 << length)-powers[odd+k])*minimum
                        for k in range(length-depth+1))
                    self.assertEqual(completion_possible(length, depth, r, odd, corr, powers), possible)

    def test_direct_resolution_preserves_all_segments(self):
        for length in (8, 14, 27):
            baseline = search(length, direct_limit=0)
            self.assertEqual(baseline["status"], "complete")
            for limit in (1, 16):
                accelerated = search(length, direct_limit=limit)
                self.assertEqual(accelerated["status"], "complete")
                self.assertEqual(accelerated["segments"], baseline["segments"])
                self.assertLessEqual(accelerated["visited_nodes"], baseline["visited_nodes"])

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
