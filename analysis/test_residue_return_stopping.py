import unittest

from residue_return_stopping import first_sampled_contraction, scan


class SampledStoppingTests(unittest.TestCase):
    def test_kernel_checked_long_witness_and_cap(self):
        self.assertIsNone(first_sampled_contraction(1689023, 224))
        self.assertEqual(first_sampled_contraction(1689023, 225),
                         dict(seed=1689023, endpoint=196274, time=225,
                              odd_steps=140, visits=45, descends=True))

    def test_later_paradoxical_visit_is_not_the_first_contraction(self):
        self.assertEqual(first_sampled_contraction(470, 46),
                         dict(seed=470, endpoint=353, time=2,
                              odd_steps=1, visits=1, descends=True))
        self.assertFalse(first_sampled_contraction(2, 2)['descends'])

    def test_censoring_is_reported_separately(self):
        result = scan(11, 1)
        self.assertEqual(result['tested_seeds'], 1)
        self.assertEqual(result['completed_seeds'], 0)
        self.assertEqual(result['censored_seeds'], [11])
        self.assertIsNone(result['longest_first_sampled_contraction'])


if __name__ == '__main__':
    unittest.main()
