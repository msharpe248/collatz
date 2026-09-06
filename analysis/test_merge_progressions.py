import json
from pathlib import Path
import unittest

from merge_progressions import compress, covers, lean_source, progression


class ProgressionTests(unittest.TestCase):
    def test_family_normalization(self):
        for Q in (0, 1, 17):
            rule = progression(dict(seed=111+4374*Q, predecessor=103+4096*Q,
                                    forward_time=1, inverse_time=12,
                                    forward_odds=1, inverse_odds=8))
            self.assertEqual((rule['seed'], rule['predecessor']), (111, 103))
            self.assertEqual((rule['seed_step'], rule['predecessor_step']), (4374, 4096))

    def test_compression_respects_residue_and_lower_bound(self):
        def rule(n, A):
            return dict(seed=n, seed_step=A, forward_time=0, inverse_time=1)
        a, b, c = rule(8, 3), rule(2, 6), rule(11, 6)
        kept = compress([a, b, c])
        self.assertEqual(len(kept), 2)
        self.assertFalse(covers(a, 2))
        self.assertTrue(covers(a, 11))
        self.assertTrue(any(covers(r, 2) for r in kept))

    def test_generated_lean_matches_saved_rules(self):
        root = Path(__file__).resolve().parents[1]
        data = json.loads((root/'analysis/merge_progressions_results.json').read_text())
        actual = (root/'lean/Collatz/MergeRuleTable.lean').read_text()
        self.assertEqual(lean_source(data), actual)


if __name__ == '__main__':
    unittest.main()
