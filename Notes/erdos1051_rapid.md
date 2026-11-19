# Erdos1051.erdos_1051.variants.rapid_growth

- Source: `FormalConjectures/ErdosProblems/1051.lean:82` (category research solved, Erdős [Er88c])
- Statement: if `a : ℕ → ℤ` is strictly increasing and `a (n+1) ≥ C · a n ^ 2` for some `C > 0`, then `∑' n, 1/(a n · a (n+1))` is irrational.
- Proof file: `results/erdos1051_rapid.lean` (identical to `work/erdos1051_rapid.lean`). It uses targeted Mathlib imports and restates the `ErdosSeries` definition verbatim.

## Proof idea
Since `a` is a strictly increasing integer sequence, `a m ≥ a 0 + m`. So there is an `N` such that for all `m ≥ N` we have `a m ≥ 1`, `C·a m ≥ 2` and `C²·a m ≥ 4`. From `N` on, `a (m+1) ≥ 2 a m`, so the terms `f m = 1/(a m a (m+1))` are positive and satisfy `f (m+1) ≤ f m / 4`. Hence the series is summable, and the tail `T n = ∑_{i≥n} f i` satisfies `0 < T n ≤ 2 f n`. Let `a'` be `a` with a possible zero entry replaced by 1. Put `q n = ∏_{k≤n} a' k` and `Q n = ∏_{k<n} a' k`. Then `p n = q n · ∑_{m<n} f m` is an integer, because each term's denominator `a m a (m+1)` divides `q n` (zero terms vanish in Lean). Suppose the sum equals `num/den`. Then `z = num·q n − den·p n` is a nonzero integer equal to `den·q n·T n`, so `|z| ≤ 2·den·g n` with `g n = |Q n| / a (n+1)`. The growth condition gives `4 a n a (n+1) ≤ a (n+2)`, hence `g (n+1) ≤ g n / 4`. So `g n → 0` geometrically, and for large `n` we get `|z| < 1`, which is a contradiction.

## Axioms
`'Erdos1051.erdos_1051.variants.rapid_growth' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-13. 2 compiles: the first was clean apart from a `push_neg` deprecation warning; the second was clean and included the axioms check.
