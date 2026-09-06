import unittest
from transfer_requests import requests, minimum_seed, missing_request_cutoff


class TransferRequestTests(unittest.TestCase):
    def test_independent_seed_scan(self):
        for N in (1, 7, 8, 15, 32, 101, 256, 4096):
            expected = {}
            for n in range(3, N, 2):
                a, m = 0, n+1
                while m%2 == 0:
                    m //= 2
                    a += 1
                if a>=2 and (3**a*m)%4 == 3:
                    v = (3**a*m-27)//36
                    expected[v] = min(expected.get(v, n), n)
            self.assertEqual(requests(N), expected)
            for v, n in expected.items():
                self.assertEqual(minimum_seed(v), n)

    def test_exhaustive_cutoff(self):
        for u in range(1, 257):
            row = missing_request_cutoff(u)
            N = row['seed_cutoff']
            self.assertTrue(all(v < u for v in requests(N)))
            newly_missing = {v for v in requests(N+1) if v >= u}
            self.assertIn(row['witness']['parameter'], newly_missing)
            self.assertEqual(minimum_seed(row['witness']['parameter']), N)

    def test_known_boundaries(self):
        self.assertEqual(missing_request_cutoff(1)['seed_cutoff'], 27)
        self.assertEqual(missing_request_cutoff(61)['seed_cutoff'], 415)
        self.assertEqual(minimum_seed(546), 511)
        self.assertEqual(len(requests(2**16)), 5461)
        with self.assertRaises(ValueError):
            missing_request_cutoff(0)


if __name__ == '__main__':
    unittest.main()
