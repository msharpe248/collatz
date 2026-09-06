import unittest

from audit_theorems import parse_axiom_output


class AxiomParserTests(unittest.TestCase):
    def test_both_lean_output_formats(self):
        output = """'A.step' does not depend on any axioms
'B.shift' depends on axioms: [propext]
'C.main' depends on axioms: [propext, Classical.choice,
 Quot.sound]
"""
        result = parse_axiom_output(output)
        self.assertEqual(result['A.step'], '')
        self.assertEqual(result['B.shift'], 'propext')
        self.assertEqual({s.strip() for s in result['C.main'].split(',')},
                         {'propext', 'Classical.choice', 'Quot.sound'})

    def test_missing_or_error_output_is_not_certified(self):
        self.assertEqual(parse_axiom_output('error: unknown constant A.missing'), {})
        self.assertNotIn('A.missing', parse_axiom_output("'B.real' depends on axioms: []"))


if __name__ == '__main__':
    unittest.main()
