"""Exact checks from the parallel route reassessment; not universal proofs."""
import json


def next_return(n):
    value, word = n, ''
    while True:
        word += str(value % 2)
        value = (3 * value + 1) // 2 if value % 2 else value // 2
        if value % 9 == 2:
            return value, word


def valuation_two(n):
    assert n != 0
    return (abs(n) & -abs(n)).bit_length() - 1


def carry_mass(n):
    carry, previous, total = 1, 0, 0
    for bit in range(n.bit_length() + 2):
        digit = (n >> bit) & 1
        carry = (digit + previous + carry) // 2
        total += carry
        previous = digit
    assert carry == previous == 0
    return total


def run():
    resets = []
    for r in (1, 2, 4, 8, 16, 32, 64):
        n = 16 * 64**r - 5
        y, w = next_return(n)
        z, v = next_return(y)
        assert w == '1101' and v == '101' and n < y < z
        assert valuation_two(11*n+23) == 5
        assert valuation_two(y+7) == 6*r
        assert 11*(y+7) == 27*(11*n+23)//16 + 54
        resets.append(dict(r=r, seed_digits=len(str(n)), incoming=5, outgoing=6*r))
    for n in range(2**16):
        assert (3*n+1).bit_count() + carry_mass(n) == 2*n.bit_count()+1
    return dict(scope='exact finite checks; carry identity not formalized here',
                reset_checks=resets, carry_seeds_checked=2**16)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
