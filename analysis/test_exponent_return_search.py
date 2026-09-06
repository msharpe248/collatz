import json
from pathlib import Path
import unittest

from exponent_return_search import census, period
from source_witness_search import trajectory


class ExponentReturnTests(unittest.TestCase):
    def test_saved_rules_at_smallest_admissible_exponent_and_lifts(self):
        data=json.loads(Path(__file__).with_name('exponent_return_search_results.json').read_text())
        for c in data['certificates']:
            t,d,M=c['depth'],c['drop'],c['modulus']
            k=c['residue']
            while k<=d:
                k+=M
            self.assertEqual(pow(3,M,2**t),1)
            for q in (0,1,3):
                exponent=k+M*q
                upper=trajectory(3**exponent+1,t)[-1]
                lower=trajectory(3**(exponent-d)+1,t)[-1]
                self.assertEqual(upper[0],lower[0])
                self.assertEqual(lower[1],upper[1]+d)
                self.assertEqual(upper[2],c['upper_correction'])
                self.assertEqual(lower[2],c['lower_correction'])

    def test_complete_small_censuses(self):
        for depth in range(1,8):
            data=census(depth,4)
            covered={c['residue'] for c in data['certificates']}
            for k in range(5,5+3*period(depth)):
                upper=trajectory(3**k+1,depth)
                found=False
                for d in range(1,5):
                    lower=trajectory(3**(k-d)+1,depth)
                    found |= any(x==y and l==j+d for (x,j,_),(y,l,_) in zip(upper,lower))
                self.assertEqual(found,k%data['modulus'] in covered)

    def test_concrete_rule(self):
        for k in (29,61,93,125):
            x,j,c=trajectory(3**k+1,7)[-1]
            y,l,e=trajectory(3**(k-1)+1,7)[-1]
            self.assertEqual((j,c,l,e),(2,76,3,58))
            self.assertEqual(x,y)
            self.assertEqual(128*x,9*3**k+85)


if __name__ == '__main__':
    unittest.main()
