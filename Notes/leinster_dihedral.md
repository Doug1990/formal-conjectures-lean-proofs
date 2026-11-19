# LeinsterGroup.dihedral_is_leinster_iff_odd_perfect

- Source: `FormalConjectures/Wikipedia/LeinsterGroup.lean:114` (category research solved)
- Statement: `DihedralGroup n` (n ≠ 0) is Leinster iff n is an odd perfect number.

Proof idea: characters χ_{p,b} : D_n → ℤ/2 (r i ↦ p(i), sr i ↦ p(i)+b) give normal
subgroups of index 2 as kernels; the rotation subgroup R = ker χ_{0,1} has order n and is
cyclic. Even n: with p the parity map ZMod n → ZMod 2, the four distinct normal subgroups
D_n, R, ker χ_{p,0}, ker χ_{p,1} already sum to 5n > 4n, so D_n is not Leinster (and n is
not odd). Odd n: every subgroup inside R is normal (conjugation by a reflection inverts
rotations); a normal subgroup containing a reflection sr i contains all rotations r(−2k)
(2 is a unit mod n) and hence everything; so the normal subgroups are D_n plus the subgroups of
the cyclic group R, which correspond to the divisors of n. Sum = 2n + σ(n), and this is 4n iff
σ(n) = 2n iff n is perfect.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-31. Compiles: 3 (1: an omega atom mismatch, a linear_combination sign, and
`show` against an unresolved function argument; 2: `rw [← nat_card]` hit the wrong
`2 * _`; 3: clean + axioms, no warnings).
