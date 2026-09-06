import unittest
from three_step_inverse_search import report,classify_base_pair
from source_witness_search import trajectory
from early_inverse_bridge_search import search
from affine_bridge_search import step

class ThreeStepInverseTests(unittest.TestCase):
    def test_geometry_and_lifted_rules(self):
        for c in report()['certificates']:
            for Q in (0,1,7):
                w=c['w']+2**c['depth']*Q
                u,v=9*w+6,8*w+5
                self.assertLess(v,u)
                self.assertEqual(trajectory(3*v+2,3)[-1][:2],(3*u+2,2))
                self.assertEqual(trajectory(27*v+20,3)[-1][:2],(243*w+175,2))
                self.assertEqual(trajectory(27*v+20,c['depth']+3)[-1][0],
                                 trajectory(27*u+20,c['depth'])[-1][0])
    def test_complete_small_census(self):
        for D in range(1,9):
            count=0
            for w in range(2**D):
                a=trajectory(243*w+175,D);b=trajectory(243*w+182,D)
                count+=any(x==y and j==k for (x,j,_),(y,k,_) in zip(a,b))
            self.assertEqual(count,search(D,multiplier=243,small=175,large=182)['levels'][-1]['covered'])
    def test_terminal_failures_and_success_are_distinct(self):
        self.assertEqual(classify_base_pair(7281),dict(kind='merge',depth=52))
        self.assertEqual(classify_base_pair(1,cap=1)['kind'],'cap')
        for w in (1,113,466033):
            c=classify_base_pair(w)
            self.assertEqual(c['kind'],'terminal_without_merge')
            x,y,j,k=c['small'],c['large'],c['small_odds'],c['large_odds']
            for _ in range(10):
                self.assertFalse(x==y and j==k)
                j,k=j+x%2,k+y%2;x,y=step(x),step(y)

if __name__=='__main__':unittest.main()
