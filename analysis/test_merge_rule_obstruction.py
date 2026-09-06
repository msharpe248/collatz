import json
from pathlib import Path
import unittest

from merge_rule_obstruction import MODULUS, replay, residue_classes, verify_table, witness


RULES = json.loads(Path(__file__).with_name('merge_progressions_results.json').read_text())['rules']


class ObstructionTests(unittest.TestCase):
    def test_finite_certificate_and_lean_classes(self):
        classes = verify_table(RULES)
        source = (Path(__file__).resolve().parents[1]/'lean/Collatz/MergeRuleObstruction.lean').read_text()
        body = source.split('def classes : List ℕ := [', 1)[1].split(']', 1)[0]
        self.assertEqual(classes, [int(x.strip()) for x in body.split(',')])
        self.assertEqual(classes[-1], MODULUS-1)

    def test_long_runs_and_inverse_edges(self):
        for horizon in (0, 1, 10, 11, 12, 64, 128):
            for q in (0, 1, 19):
                replay(RULES, horizon, q)

    def test_stationary_ternary_class_and_input_validation(self):
        for k in (11, 12, 100):
            self.assertEqual((3**k*pow(2**k, -1, 3**11)-1) % 3**11,
                             residue_classes()[-1] % 3**11)
        for h, q in [(-1, 0), (0, -1)]:
            with self.assertRaises(ValueError):
                witness(h, q)


if __name__ == '__main__':
    unittest.main()
