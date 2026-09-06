import json
from pathlib import Path
import unittest

from merge_chain_search import RuleIndex
from odd_run_merges import check, seed
from word_surgery import orbit


class OddRunMergeTests(unittest.TestCase):
    def test_both_branches_inside_obstruction(self):
        rules = json.loads(Path(__file__).with_name('merge_progressions_results.json').read_text())['rules']
        ix = RuleIndex(rules)
        for a in (18, 19, 20, 32, 64, 128):
            for q in (0, 1, 13):
                for branch in (True, False):
                    check(ix, a, q, branch)

    def test_all_small_odd_parts(self):
        for a in range(1, 21):
            for m in range(1, 40, 2):
                n = 2**a*m-1
                end, odds = orbit(n, a)
                self.assertEqual((end+1, odds), (3**a*m, a))
                x = orbit(n, a+2)[0]
                y = orbit(n-1, a+2)[0]
                if (3**a*m) % 4 == 1:
                    self.assertEqual(x, y)
                else:
                    self.assertEqual(x, 9*y+2)

    def test_bad_input(self):
        for a, q in ((0, 0), (1, -1)):
            with self.assertRaises(ValueError):
                seed(a, q)


if __name__ == '__main__':
    unittest.main()
