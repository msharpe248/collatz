import unittest

from mersenne_exit_search import census, signature
from mersenne_inverse_prefix import predicted
from source_witness_search import trajectory


class MersenneExitTests(unittest.TestCase):
    def test_exit_identity(self):
        for h in range(100):
            k = 6 * h + 4
            x, j, y, l = predicted(k, k)
            self.assertEqual((x, y), (3 ** (4 * h + 5) - 7,
                                      3 ** (4 * h + 6) - 10))
            self.assertEqual(l, j + 1)

    def test_complete_small_census(self):
        # Independent full integer trajectories, including affine corrections.
        for depth in (8, 12):
            modulus = 2 ** (depth - 2)
            expected = 0
            for r in range(1, modulus, 4):
                e = r + modulus
                X = 3 ** e
                a = trajectory(X - 7, depth)
                b = trajectory(3 * X - 10, depth)
                direct = next((t for t in range(1, depth + 1)
                               if a[t][0] == b[t][0]
                               and a[t][1] == b[t][1] + 1), None)
                hit = signature(pow(3, r, 2 ** depth), depth)
                self.assertEqual(direct, hit['depth'] if hit else None)
                expected += direct is not None
            self.assertEqual(census(depth)['covered'], expected)

    def test_all_symbolic_rules(self):
        result = census(16)
        self.assertEqual((result['covered'], result['eligible']), (110, 4096))
        for rule in result['rules']:
            t = rule['depth']
            for Q in (1, 2, 7, 2 ** 32):
                X = rule['power_residue'] + 2 ** t * Q
                a = trajectory(X - 7, t)[-1]
                b = trajectory(3 * X - 10, t)[-1]
                self.assertEqual(a[0], b[0])
                self.assertEqual(a[1], b[1] + 1)
                self.assertEqual(2 ** t * a[0],
                                 rule['coefficient'] * X + rule['correction'])
            k = rule['mersenne_k_residue']
            for lift in (0, 1, 3):
                K = k + lift * rule['mersenne_k_modulus']
                self.assertEqual(K % 6, 4)
                e = 4 * ((K - 4) // 6) + 5
                self.assertEqual(pow(3, e, 2 ** t), rule['power_residue'])

    def test_first_rule(self):
        rule = census(12)['rules'][0]
        self.assertEqual((rule['exponent_residue'], rule['exponent_modulus'],
                          rule['mersenne_k_residue'], rule['mersenne_k_modulus']),
                         (981, 1024, 1468, 1536))
        self.assertEqual((rule['coefficient'], rule['correction']), (729, -187))
        # Verify the complete prefix and exit for the first actual Mersenne k.
        k = 1468
        a = trajectory(27 * 2 ** k - 14, k + 12)[-1][0]
        b = trajectory(27 * 2 ** k - 7, k + 12)[-1][0]
        self.assertEqual(a, b)


if __name__ == '__main__':
    unittest.main()
