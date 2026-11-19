# Erdos939.erdos_939.variants.infinite_of_six_le (+ variants.finite)

- Source: `FormalConjectures/ErdosProblems/939.lean`, lines 92 (`infinite_of_six_le`, research solved) and 77 (`variants.finite`, research solved, a corollary with r = 6).
- Verified file: `work/erdos939_six.lean`. `results/erdos939_six.lean` is a hand copy of it. `Nat.Full`, `Finset.Coprime` and `Erdos939Sums` are restated locally with the same definitions, because the build uses targeted Mathlib imports instead of FormalConjecturesUtil.

**Proof idea.** This is the construction from the forum thread. Let M = 4^r and B = M!. Take any prime q > B, and set X = q^r and Y = B^r. Expanding the binomial gives (X+Y)^r = (X−Y)^r + Σ_{m odd ≤ r} 2C(r,m)·Y^m X^(r−m). The m = 3 term is split into k = r/2 − 2 pieces (i+1)·2C(r,3)·(B/S_k)·B^(2r−1)·(B q^(r−3))^r, where S_k = 1+…+k ≤ r² divides B. Every coefficient is at most 4^r, so it divides B, and so every summand has the form a·b^r with every prime of a dividing b, which makes it r-full. The sum is the r-th power (q^r+B^r)^r, so it is r-full too. The summands are pairwise distinct: the T_m are separated by their q-adic valuations (r−m)·r, the pieces of m = 3 by their factor i+1, and (X−Y)^r is the only odd summand. Counting gives ((r+1)/2 − 1) + (r/2 − 2) + 1 = r − 2 summands. gcd((X−Y)^r, T_1) = 1 because q ∤ B and every prime of 2r divides B. The sum grows with q, so infinitely many primes q give infinitely many sets (`Set.Infinite.of_image` + `Set.infinite_of_forall_exists_gt`).

**Axioms:** `propext, Classical.choice, Quot.sound` (for both theorems).

Date: 2026-11-08.
