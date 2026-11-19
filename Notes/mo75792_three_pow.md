# Mathoverflow75792.complexity_three_pow

- Source: `FormalConjectures/Mathoverflow/75792.lean:213` (category research solved; Selfridge, see arXiv:1207.4841)
- Statement: `∀ n : ℕ, 0 < n → complexity (3 ^ n) = 3 * n`
- Date: 2026-11-01
- Compiles: 2 (1: `interval_cases` not loaded with these imports, `Nat.pos_pow_of_pos` unknown; 2: clean)

## Proof idea
Upper bound: `Reachable.pow 3 n` gives an expression with 3n ones. Lower bound: by induction on
`Reachable m k` we show `1 ≤ m ∧ 1 ≤ k ∧ m^3 ≤ 3^k` (i.e. ‖m‖ ≥ 3 log₃ m). Products are immediate.
For sums with both summands ≥ 2, m + n ≤ mn. For a summand 1, (1+n)³ ≤ 3n³ ≤ 3^a·3^b when n ≥ 3;
n = 1 gives 8 ≤ 3^(a+b) with a+b ≥ 2, and n = 2 forces b ≥ 2 (8 ≤ 3^b), so 27 ≤ 3^(a+b).
Applied to the minimal expression for 3^n: 3^(3n) ≤ 3^complexity, hence 3n ≤ complexity.
The file restates the definitions of the source (Reachable, its decision procedure, complexity)
verbatim with targeted imports.

## Axioms
`'Mathoverflow75792.complexity_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]`
