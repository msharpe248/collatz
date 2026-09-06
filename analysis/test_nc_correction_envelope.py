from pathlib import Path
import unittest

from nc_correction_envelope import envelope, lean_table, verify
from word_surgery import orbit


class EnvelopeTests(unittest.TestCase):
    def test_finite_certificate_and_boundary(self):
        self.assertEqual(verify(envelope(31)), [])
        self.assertIn((32, 21), verify(envelope(32)))

    def test_matches_lean_data(self):
        root = Path(__file__).resolve().parents[1]
        text = (root/'lean/Collatz/NCPrefixInjective.lean').read_text()
        self.assertIn(lean_table(envelope(31)), text)

    def test_actual_boundary_seed(self):
        n = 3384695803
        y, j = orbit(n, 32)
        self.assertEqual(j, 21)
        d = 2**32*y-3**j*n
        self.assertEqual(d, 54020229503)
        self.assertTrue(all(2**i <= 3**orbit(n, i)[1] for i in range(33)))
        self.assertGreaterEqual(d+2**j, 5*3**j)


if __name__ == '__main__':
    unittest.main()
