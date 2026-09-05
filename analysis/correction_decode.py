"""Exact finite correction reconstruction, matching Collatz.CorrectionDecode.

Tested Python, not Lean-extracted code. This decides one correction, not
whether a range of lengths or corrections contains a paradoxical segment.
"""


def word_correction(word):
    value = 0
    for i, bit in enumerate(word):
        value = 3*value+(1 << i) if bit else value
    return value


def decode_correction(length, odd, correction):
    """Return the unique matching word or None; reject invalid natural inputs."""
    if min(length, odd, correction) < 0:
        raise ValueError("natural parameters required")
    count, value = odd, correction
    word = []
    for _ in range(length):
        if value % 2 == 0:
            word.append(0)
            value //= 2
        else:
            word.append(1)
            count = max(count-1, 0)
            value = max(value-3**count, 0)//2
    # These checks are essential: truncated subtraction cannot certify data.
    if sum(word) != odd or word_correction(word) != correction:
        return None
    return tuple(word)
