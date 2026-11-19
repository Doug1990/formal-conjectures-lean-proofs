# Erdos263.erdos_263.variants.sub_doubly_exponential

- Source: `FormalConjectures/ErdosProblems/263.lean:107` (category research solved, Kovač–Tao 2024)
- Statement: if `a` is strictly increasing, `Σ 1/a n` converges and `a (n+1) / a n ^ 2 → 0`, then `a` is not an irrationality sequence.
- Verified file: `work/erdos263_sub.lean` (this file is a hand copy of it). `IsIrrationalitySequence` is restated verbatim from the source.

Proof idea: the greedy interval lemma from `results/erdos264_i.lean`, generalised to a variable number `K n` of choices at step `n`. Put `K (m+1) = ⌊2a(m+1)²/a(m)²⌋ + 1`. Then `K n / a n ≤ 2·a(n+1)/a(n)² + 1/a(n+1) → 0`, so from some index `N0` on we have `K n ≤ a n`. For `n ≥ N0` the choices are `b n = a n + j` with `0 ≤ j ≤ K n`. Each step of the choice `1/(a n + j)` is at most `1/a n²`. The spread `1/a_{n+1} − 1/(a_{n+1}+K_{n+1})` of the next term is at least `K_{n+1}/(2a_{n+1}²) ≥ 1/a_n²`. So the greedy algorithm reaches every value between the lowest and highest tail sum, and in particular a rational one (`exists_rat_btwn`). For `n < N0` take `b n = a n`. Then `|a n / b n − 1| ≤ K n / a n → 0`, while `Σ 1/b n = q` is rational. This contradicts the definition.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-10
