import unittest
from paradoxical_cylinders import orbit, step


def finite_orbit(seed, work_limit=10000):
    states, first = [], {}
    value = seed
    while value not in first:
        if len(states) == work_limit:
            raise RuntimeError('orbit not resolved within the control work limit')
        first[value] = len(states)
        states.append(value)
        value = step(value)
    return states, first[value]


def full_factors(states, cycle_start, length):
    period = len(states)-cycle_start
    def parity(i):
        if i >= len(states):
            i = cycle_start+(i-cycle_start) % period
        return states[i] % 2
    return {tuple(parity(t+i) for i in range(length)) for t in range(len(states))}


class ParityComplexityControls(unittest.TestCase):
    def test_finite_prefix_factor_floor(self):
        checked = 0
        for seed in range(1, 501):
            K = seed.bit_length()  # seed+1 <= 2^K
            for q in range(11):
                L, starts = 3*q+K, 5*q+1
                values = orbit(seed, starts+L)
                if len(set(values[:starts])) != starts:
                    continue
                self.assertTrue(all(x < 1 << L for x in values[:starts]))
                factors = {tuple(x % 2 for x in values[t:t+L]) for t in range(starts)}
                self.assertEqual(len(factors), starts)
                checked += 1
        self.assertGreater(checked, 1000)

    def test_global_factors_for_resolved_controls(self):
        for seed in range(201):
            states, cycle_start = finite_orbit(seed)
            for length in range(21):
                factors = full_factors(states, cycle_start, length)
                self.assertLessEqual(len(factors), max(states)+1)
                # Direct replay far enough to cover every transient/cycle start.
                values = orbit(seed, len(states)+length)
                replay = {tuple(x % 2 for x in values[t:t+length]) for t in range(len(states))}
                self.assertEqual(factors, replay)
        states, start = finite_orbit(1)
        self.assertEqual(len(full_factors(states, start, 0)), 1)
        for length in range(1, 21):
            self.assertEqual(len(full_factors(states, start, length)), 2)


if __name__ == '__main__':
    unittest.main()
