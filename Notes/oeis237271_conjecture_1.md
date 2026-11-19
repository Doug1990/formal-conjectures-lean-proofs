# OeisA237271.conjecture_1

- Source: `FormalConjectures/OEIS/237271.lean`, line 132: `a n = A001227 n - A239657 n` for 0 < n. Category: research solved (Hoft).
- Proof file: `results/oeis237271_conjecture_4_5.lean`, which also contains conjecture_2/3/4/5. It is an identical copy of the verified `work/oeis237271_c45.lean`. The A001227 / A239657 defs are copied verbatim; they sit after conjecture_5 instead of before conjecture_1.

**Proof idea.** a(n) − 1 is the card of T = consecutive divisor pairs (x, y) with y odd and y ≥ 2x (zip list nodup + `mem_zip`). The odd divisors split into those with a divisor d satisfying d < m < 2d (A239657) and the rest C. For an odd divisor m > 1, let x be its predecessor (the max of the divisors below m). Then m ∈ C iff 2x ≤ m iff (x, m) ∈ T. So C = {1} ∪ snd(T), where snd is injective on T (the predecessor is unique) and 1 ∉ snd(T). Hence |C| = |T| + 1 = a(n), and A001227 = A239657 + |C|.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-06
