from fractions import Fraction
import unittest

from source_witness_search import follow_rank, inspect_seed, power_two_terminal, trajectory


class SourceWitnessTests(unittest.TestCase):
    def test_terminal_family_and_first_hit(self):
        for m in range(201):
            row = power_two_terminal(m)
            self.assertEqual(row['terminal_target'],3**(m+2)+1)
            self.assertEqual(row['slope'],str(3**(m+2)))

    def test_initial_test_misses_successor_failure(self):
        self.assertEqual(inspect_seed(1)['status'],'candidate')
        row = follow_rank(1)
        self.assertEqual((row['status'],row['source'],row['target']),
                         ('greedy_dead_end',8,47))
        self.assertEqual((row['slope'],row['offset']),('6','-1'))
        # Independently derive slopes from step products rather than the
        # explorer's exponent state and test every allowed advance pair.
        def paths(n):
            a,b=Fraction(1),Fraction(0)
            result=[(n,a,b)]
            for _ in range(12):
                c=3 if n%2 else 1
                d=1 if n%2 else 0
                a,b=c*a/2,(c*b+d)/2
                n=(c*n+d)//2
                result.append((n,a,b))
            return result
        def valuation(n,p):
            k=0
            while n%p==0:
                n//=p;k+=1
            return k
        for x,a,b in paths(8):
            for y,c,d in paths(47):
                slope=6*c/a
                i=valuation(slope.numerator,2)-valuation(slope.denominator,2)
                j=valuation(slope.numerator,3)-valuation(slope.denominator,3)
                self.assertNotEqual(x,y)
                self.assertNotEqual(y,1)
                self.assertGreaterEqual((abs(i)+abs(j),abs(y-x)),(2,39))

    def test_depth_failure_is_not_global(self):
        self.assertEqual(follow_rank(1,depth=100)['status'],'terminal')
        self.assertEqual(follow_rank(1,macro_cap=0)['status'],'macro_cap')


if __name__ == '__main__':
    unittest.main()
