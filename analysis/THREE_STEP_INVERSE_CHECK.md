# Three-step inverse template — 2026-09-05

The previous checkpoint 699509e proved an early inverse family in u=2 modulo
three. This experiment extends the template to u=6 modulo nine, including
Mersenne parameters with exponent k=4 modulo six. No universal coverage is proved.

## Exact candidate rule

For u=9w+6 and v=8w+5:

    v<u,
    T^3(3v+2)=3u+2,
    T^3(27v+20)=243w+175,
    27u+20=243w+182.

The first three-step path has parity odd/even/odd:
24w+17 ->36w+26 ->18w+13 ->27w+20.
The auxiliary larger path has parity odd/odd/even:
216w+155 ->324w+233 ->486w+350 ->243w+175.
Both have two odd steps. Thus transfer at v supplies convergence of the lower
endpoint in a pair separated by seven, before any target-cycle assumption.

A same-clock, same-odd-count merge of that pair extends uniformly over the
binary w-cylinder. The generic early-inverse search now accepts its multiplier
and two offsets as keyword parameters, preserving the preceding template as the
default. The first new rule has w=25 modulo 128:

    u=231+1152Q,     v=205+1024Q,
    T^3(3v+2)=3u+2,
    T^10(27v+20)=T^7(27u+20)=440+2187Q.

These are exact experimental certificates with a written affine-lifting argument.
They are not newly formalized Lean declarations, and the smaller transfer premise
remains required.

## Complete bounded census

Through depth twelve, 70 first rules cover 204 of 4096 binary w-residues and leave
3892 unresolved. Tests independently compare the complete small-depth census
with integer trajectories and replay every saved rule at Q=0,1,7, including both
three-step geometries and strict parameter decrease. The old template's tests
continue to pass. The census is not kernel certified.

## Mersenne probes change the next action

The base parameter u=15 corresponds to w=1. At comparison clock 38 the reduced
pair is (1,2), so it never subsequently coalesces at aligned times. The same
phase obstruction occurs at exponent k=10. At k=22 the endpoints do meet in the
cycle, but their accumulated odd counts differ permanently, preventing a uniform
same-count cylinder merge. At k=16 a valid merge occurs at comparison time 52.

These terminal checks certify all-later failure of this particular merge
criterion for the individual tested exponents. They do not exclude other inverse
paths or multi-bridge configurations, and do not establish an infinite family of
failures. The isolated success at k=16 is not a proof of every exponent in its
congruence class.

The three-step template therefore expands the repertoire but still cannot supply
universal coverage of its own parameter class. Increasing its time limit will
not repair the three terminal failures. A further step should change the inverse
path or use additional smaller-transfer instances, rather than merely extending
these same paired trajectories. This is an experimental research log, not a new
significant Lean milestone or a claim of mathematical priority.

Reproduce with `python3 analysis/three_step_inverse_search.py`.
Run `python3 -m unittest discover -s analysis -p 'test_*inverse*py'`.

Subsequent result: `Collatz.TwoEarlyBridges` verifies that an additional
smaller transfer instance resolves the base-15 failure on an infinite parameter
progression. The original single-template failure remains correct; it did not
exclude that two-premise path. See `paper/two_early_bridges.tex`.
