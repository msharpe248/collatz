import json
from pathlib import Path
import unittest

from affine_bridge_search import step
from cycle_bridge_search import charge, construct
from test_affine_bridge_search import replay


class CycleBridgeTests(unittest.TestCase):
    def test_saved_certificates_replay(self):
        data=json.loads(Path(__file__).with_name('cycle_bridge_search_results.json').read_text())
        for row in data['rows']:
            self.assertEqual(row,construct(row['parameter']))
            if row['kind']=='certificate':
                for q in (0,1,7):
                    replay(row,q)
                self.assertEqual(len(row['bridges']),row['initial_gap'])

    def test_cycle_invariant_and_bridge_increment(self):
        for t in range(20):
            for p in range(1,20):
                for x in (1,2):
                    self.assertEqual(charge(x,p,t),charge(step(x),p+x%2,t+1))
                x,pp,tt=20,p+2,t
                for _ in range(7):
                    pp,tt=pp+x%2,tt+1
                    x=step(x)
                self.assertEqual(x,2)
                self.assertEqual(charge(x,pp,tt),charge(2,p,t)+1)

    def test_negative_gap_and_caps_are_distinct(self):
        self.assertEqual(construct(4)['kind'],'negative_cycle_gap')
        self.assertEqual(construct(4)['gap'],-1)
        self.assertEqual(construct(4,cap=1)['kind'],'base_orbit_cap')
        with self.assertRaises(ValueError):
            construct(0)
        # Equality of charge at one clock determines both state and exponent.
        for t in range(10):
            states=[(x,p) for x in (1,2) for p in range(1,10)]
            self.assertEqual(len({charge(x,p,t) for x,p in states}),len(states))


if __name__=='__main__':
    unittest.main()
