import unittest
from mersenne_inverse_prefix import predicted,check,report

class MersennePrefixTests(unittest.TestCase):
    def test_complete_prefixes(self):
        for k in range(101):check(k)
    def test_phase_boundaries(self):
        for k in (1,2,3,4,10,64):
            x,j,y,l=predicted(k,k)
            self.assertGreater(x,0);self.assertGreater(y,0)
            if k%3==2:self.assertEqual((j-l,y-x),(0,5))
            else:self.assertEqual(j-l,-1)
        with self.assertRaises(ValueError):predicted(4,5)
    def test_probe_limits_preserved(self):
        rows=report()['probes']
        self.assertEqual([r['exponent'] for r in rows if r['kind']=='depth_limit'],[10,28])
        self.assertTrue(all(r['depth']>r['exponent'] for r in rows if r['kind']=='certificate'))

if __name__=='__main__':unittest.main()
