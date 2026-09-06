import unittest
from early_inverse_bridge_search import search
from source_witness_search import trajectory

class EarlyInverseBridgeTests(unittest.TestCase):
    def test_complete_small_census(self):
        for D in range(1,9):
            count=0
            for w in range(2**D):
                a=trajectory(81*w+71,D);b=trajectory(81*w+74,D)
                count+=any(x==y and j==k for (x,j,_),(y,k,_) in zip(a,b))
            self.assertEqual(count,search(D)['levels'][-1]['covered'])
    def test_all_lifted_rules(self):
        for c in search()['certificates']:
            for Q in (0,1,7):
                w=c['w']+2**c['depth']*Q
                u,v=3*w+2,2*w+1
                self.assertLess(v,u)
                self.assertEqual(trajectory(3*v+2,1)[-1][0],3*u+2)
                self.assertEqual(trajectory(27*v+20,c['depth']+1)[-1][0],
                                 trajectory(27*u+20,c['depth'])[-1][0])
    def test_first_rule(self):
        self.assertEqual(search(6)['certificates'],[dict(w=19,depth=6,endpoint=227,odds=2)])

if __name__=='__main__':unittest.main()
