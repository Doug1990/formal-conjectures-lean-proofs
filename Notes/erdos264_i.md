# Erdős 264 parts.i: 2^n is not an irrationality sequence (Kovač–Tao)

- Statement: `Erdos264.erdos_264.parts.i : ¬IsIrrationalitySequence (2 ^ ·)` (research solved),
  source `FormalConjectures/ErdosProblems/264.lean:56` in the checkout.
- Proof idea: an interval argument. For n ≥ 4 let b_n range over {1,…,17}. The possible terms
  1/(2^n + b_n) have consecutive gaps ≤ 4^{-n}, and the spread of the next index,
  1/(2^{n+1}+1) − 1/(2^{n+1}+17), is at least that large. So a generic greedy lemma
  (`Greedy.greedy`: choices f n j antitone in j, nonnegative, summable top choices, and gap ≤
  spread of index n+1 ⇒ every t between the sum of the lowest and the sum of the highest choices
  is exactly Σ f n (c n) for some c with c n ≤ K) hits every value in a nondegenerate interval.
  The greedy picks the largest admissible term each step and keeps the remainder between the low
  and high tails, which tend to 0. Pick a rational q so that q − 103/90 is in that interval. Set
  b_n = 1 for n < 4 (those terms sum to 1/2+1/3+1/5+1/9 = 103/90), and b_{n+4} = c n + 1.
  Then Σ 1/(2^n + b_n) = q. b is bounded, nonzero, and 2^n + b_n ≠ 0, so the sum must be
  irrational, which is a contradiction.
- Axioms: `[propext, Classical.choice, Quot.sound]`
- Definition `IsIrrationalitySequence` restated verbatim; `@[category]` attributes dropped.
- Date: 2026-11-01
