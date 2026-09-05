import itertools
import unittest
from correction_decode import decode_correction, word_correction
from paradoxical_cylinders import orbit


class CorrectionDecodeControls(unittest.TestCase):
    def test_roundtrip_all_words(self):
        for length in range(11):
            for word in itertools.product((0, 1), repeat=length):
                self.assertEqual(decode_correction(length, sum(word), word_correction(word)), word)

    def test_acceptance_matches_exhaustive_attainable_sets(self):
        for length in range(8):
            expected = {(sum(w), word_correction(w)): w
                        for w in itertools.product((0, 1), repeat=length)}
            self.assertEqual(len(expected), 1 << length)
            for odd in range(length+2):
                for correction in range(3**length+2):
                    self.assertEqual(decode_correction(length, odd, correction),
                                     expected.get((odd, correction)))
        for params in ((-1, 0, 0), (1, -1, 0), (1, 0, -1)):
            with self.assertRaises(ValueError):
                decode_correction(*params)

    def test_actual_and_artificial_paradoxical_data(self):
        for seed in (7, 9, 18, 19, 25):
            values = orbit(seed, 8)
            word = tuple(v % 2 for v in values[:-1])
            odd = sum(word)
            correction = 256*values[-1]-3**odd*seed
            self.assertEqual(decode_correction(8, odd, correction), word)
        # The previous paper's artificial exact return is not attained.
        self.assertEqual(3**6*3+194421, 2**16*3)
        self.assertIsNone(decode_correction(16, 6, 194421))


if __name__ == '__main__':
    unittest.main()
