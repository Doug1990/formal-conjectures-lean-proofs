# OeisA237271.conjecture_4 and conjecture_5

- Source: `FormalConjectures/OEIS/237271.lean`, lines 168 (conjecture_4, Odd (a (n^2))) and 180 (conjecture_5, Odd (a (n*(2n-1)))). Category: research solved.
- Verified file: `work/oeis237271_c45.lean`. This file is an identical copy.

**Proof idea.** By conjecture_2/3 (re-proved in the file), a(n) = 1 + the number of consecutive divisor pairs (x, y) with y > 2x. The count is turned into the card of a Finset S of such "jump" pairs: the zip list is nodup, and its members are exactly the consecutive divisor pairs. The map (x, y) ↦ (n/y, n/x) is an involution on S, because it keeps consecutiveness and the jump condition. It swaps the pairs with xy < n and the pairs with xy > n. So if no jump pair has xy = n, |S| is even and a(n) is odd. For n = m², a pair with xy = m² would have m strictly between x and y. For n = m(2m−1), x < m forces m strictly between x and y, and x ≥ m gives xy > 2m² > n. So neither case has such a pair.

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-06
