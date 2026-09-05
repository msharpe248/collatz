"""Exact finite controls for the endpoint cancellation and its coverage gap.
The universal arithmetic obstruction is proved in Lean. Rational mechanical
rotation coverage now has a uniform Lean proof in RationalGrid; these are
independent finite regression controls.
"""
from fractions import Fraction
from itertools import product
from math import gcd
import unittest


def correction(word):
    c, ones = 0, 0
    for bit in reversed(word):
        c = bit * 3**ones + 2*c
        ones += bit
    return c


def rotations(word):
    return {word[i:] + word[:i] for i in range(len(word))}


def endpoint_witness(word):
    rots = rotations(word)
    for w in sorted(rots):
        if w[0] == 1 and w[-1] == 0:
            swapped = (0,) + w[1:-1] + (1,)
            if swapped in rots:
                return w, swapped
    return None


class EndpointCycleControls(unittest.TestCase):
    def test_cancellation_all_short_middles(self):
        for length in range(13):
            for u in product((0, 1), repeat=length):
                left, right = (1,) + u + (0,), (0,) + u + (1,)
                a, b = 2**(length+2), 3**(sum(u)+1)
                self.assertEqual(3*correction(left)+a,
                                 correction(right)+b+2**(length+1))
                if b < a:
                    both_integral = correction(left) % (a-b) == 0 and correction(right) % (a-b) == 0
                    self.assertEqual(both_integral, length == 0)

    def test_primitive_mechanical_rotations(self):
        checked = 0
        for q in range(2, 81):
            for p in range(1, q):
                if gcd(p, q) != 1:
                    continue
                word = tuple(((i+1)*p)//q - (i*p)//q for i in range(q))
                self.assertIsNotNone(endpoint_witness(word), (p, q))
                checked += 1
        self.assertGreater(checked, 1900)

    def test_real_intercept_grid_translation(self):
        def floor(x):
            return x.numerator // x.denominator

        for q in range(2, 31):
            phases = (Fraction(-7, 3), Fraction(-1), Fraction(0),
                      Fraction(1, 2*q), Fraction(q-1, q),
                      Fraction(2*q-1, 2*q), Fraction(3, 2))
            for p in range(1, q):
                for rho in phases:
                    beta = rho - floor(rho)
                    r = floor(q*beta)
                    for t in range(2*q+1):
                        mechanical = floor((t+1)*Fraction(p, q)+rho) - floor(t*Fraction(p, q)+rho)
                        grid = int((t*p+r) % q + p >= q)
                        self.assertEqual(mechanical, grid, (p, q, rho, t))
        for seed, rho in ((1, Fraction(1, 2)), (2, Fraction(0))):
            value = seed
            for t in range(100):
                mechanical = floor(Fraction(t+1, 2)+rho) - floor(Fraction(t, 2)+rho)
                self.assertEqual(value % 2, mechanical)
                value = (3*value+1)//2 if value % 2 else value//2

    def test_rotation_witness_is_not_universal(self):
        # This is a rational cycle candidate (19/5), not an integer counterexample.
        self.assertIsNone(endpoint_witness((1, 1, 1, 0, 0)))
        self.assertEqual(correction((1, 1, 1, 0, 0)), 19)
        self.assertEqual(2**5 - 3**3, 5)
        self.assertEqual(endpoint_witness((1, 0)), ((1, 0), (0, 1)))


if __name__ == '__main__':
    unittest.main()
