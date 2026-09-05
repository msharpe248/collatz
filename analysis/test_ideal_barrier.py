import unittest
from paradoxical_cylinders import step


class IdealBarrierControls(unittest.TestCase):
    def test_finite_geometric_lower_bound(self):
        for seed in range(201):
            value, odd = seed, 0
            for t in range(51):
                correction = (1 << t)*value-3**odd*seed
                self.assertGreaterEqual(correction+(1 << odd), 3**odd)
                odd += value % 2
                value = step(value)
        for length in range(1, 21):
            seed, value = (1 << length)-1, (1 << length)-1
            for _ in range(length):
                self.assertEqual(value % 2, 1)
                value = step(value)
            correction = (1 << length)*value-3**length*seed
            self.assertEqual(correction, 3**length-(1 << length))

    def test_strict_certificate_after_first_even(self):
        for seed in range(1, 501):
            value, odd, t = seed, 0, 0
            while value % 2:
                value = step(value)
                odd += 1
                t += 1
            value = step(value)
            t += 1
            correction = (1 << t)*value-3**odd*seed
            # Conditional on tail limit >= 1, this finite inequality
            # makes the original limit strictly greater than one.
            self.assertGreater(correction+(1 << t), 3**odd)


if __name__ == '__main__':
    unittest.main()
