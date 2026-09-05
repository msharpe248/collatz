import unittest
from paradoxical_cylinders import orbit, step


class OddPrehistoryControls(unittest.TestCase):
    def test_explicit_histories(self):
        exponents = {1: 4, 2: 3, 4: 6, 5: 3, 7: 4, 8: 5}
        for target in range(1, 1000, 2):
            if target % 3 == 0:
                continue
            seed, total = target, 0
            for count in range(11):
                values = orbit(seed, total)
                self.assertEqual(values[-1], target)
                self.assertEqual(sum(x % 2 for x in values[:-1]), count)
                self.assertGreaterEqual(seed, target+count)
                self.assertLessEqual(3*count, total)
                self.assertLessEqual(total, 6*count)
                self.assertTrue(all(x % 3 for x in values))
                a = exponents[seed % 9]
                previous = ((1 << a)*seed-1)//3
                self.assertGreater(previous, seed)
                self.assertEqual(previous % 2, 1)
                self.assertNotEqual(previous % 3, 0)
                seed, total = previous, total+a

    def test_sibling_merger(self):
        for n in range(1, 1000, 2):
            values = orbit(4*n+1, 3)
            self.assertEqual(values[2], 3*n+1)
            self.assertNotEqual(values[2], n)
            self.assertEqual(values[3], step(n))


if __name__ == '__main__':
    unittest.main()
