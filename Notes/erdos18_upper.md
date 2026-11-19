# Erdos18.erdos_18_upper_bound

- Source: `FormalConjectures/ErdosProblems/18.lean:266` (category research solved). Statement: `∀ᶠ n in atTop, practicalH n! < n`.
- Proof idea: this strengthens the induction that shows n! is practical (the file's `factorial_isPractical`). Lemma `rep`: for n ≥ 2, every m ≤ n! is a sum of at most n − 1 distinct divisors of n!. Base case 2! = 2. Step: write m = (n+1)q + r with q ≤ n! and r < n+1, represent q with ≤ n − 1 divisors of n!, multiply each by n+1 to get divisors of (n+1)! (injective), and add r as a further divisor when r ≠ 0. r is a divisor because 1 ≤ r ≤ n, and it is distinct from the scaled divisors, which are ≥ n+1. So the count is ≤ n. For n ≥ 2 each inner sInf in practicalH is ≤ n − 1 < n, and `Finset.sup_lt_iff` finishes.
- `subsetSums` is restated locally, identical to the FormalConjecturesForMathlib definition, because the work files use targeted Mathlib imports only.
- Axioms: `'Erdos18.erdos_18_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-08. 1 compile (clean + axioms).
