import unittest
from two_early_bridges import search,replay

class TwoEarlyBridgeTests(unittest.TestCase):
    def test_complete_sample_replays(self):
        for w in range(256):
            c=search(w)
            if c['kind']=='certificate':
                for Q in (0,1,7):replay(c,Q)
    def test_mersenne_base_requires_extra_bridge(self):
        self.assertEqual(search(1,max_extra=0)['kind'],'depth_limit')
        c=search(1)
        self.assertEqual((c['depth'],c['endpoint'],c['exponent']),(40,2,25))
        self.assertEqual(c['extra'],[dict(time=25,parameter=2,exponent=16)])
    def test_cap_is_reported(self):
        self.assertEqual(search(1,state_cap=1)['kind'],'state_cap')

if __name__=='__main__':unittest.main()
