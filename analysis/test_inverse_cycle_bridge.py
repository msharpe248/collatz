import unittest
from inverse_cycle_bridge import construct,replay
from source_witness_search import trajectory

class InverseCycleBridgeTests(unittest.TestCase):
    def test_entire_sample_replays(self):
        for u in range(16,1001):
            c=construct(u)
            self.assertEqual(c['kind'],'certificate')
            for Q in (0,1,7):replay(c,Q)
    def test_macro_geometry(self):
        self.assertEqual(trajectory(47,65)[-1][:2],(2,38))
        self.assertEqual(trajectory(425,38)[-1][:2],(2,19))
        self.assertEqual(2*(-38+2+19)-(-65+38),-7)
    def test_retreat_requires_maximum_clock_modulus(self):
        c=construct(20)
        self.assertEqual(c['negative_excursions'],2)
        self.assertEqual(c['depth'],133)
        self.assertEqual(c['operations'][0]['length'],133)
        self.assertEqual(construct(20,cap=1)['kind'],'base_cap')
        self.assertEqual(construct(16,cap=82)['kind'],'construction_cap')
        with self.assertRaises(ValueError):construct(15)

if __name__=='__main__':unittest.main()
