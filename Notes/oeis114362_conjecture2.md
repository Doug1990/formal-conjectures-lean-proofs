# OeisA114362.conjecture2

- Source: `FormalConjectures/OEIS/114362.lean:105` (category research solved), checkout of formal-conjectures
- Statement: with t(n) = ζ(2n)/ζ(n)², (1 − t)/(1 + t) − (2^−n + 3^−n + 5^−n + 7^−n) = O(11^−n).
- Verified file: work/oeis114362_c2.lean (results/oeis114362_conjecture2.lean is an identical copy). Statement and the def `t` are copied verbatim; FormalConjecturesUtil is replaced by targeted Mathlib imports.

## Proof idea
(1 − t)/(1 + t) − S = ((1−S)ζ(n)² − (1+S)ζ(2n)) / (ζ(n)² + ζ(2n)), and the denominator is ≥ 2. Split ζ(n) = P + R1 (P = Σ_{k≤10} k^−n) and ζ(2n) = Q + R2 (Q = 1 + 4^−n + 9^−n). Both tails are ≤ 11^−n · Σ 121/(k+1)², via (11/m)^n ≤ (11/m)² for n ≥ 2. The main part (1−S)P² − (1+S)Q is a finite Dirichlet combination E(f) with f(k) = k^−n, which is multiplicative. Write f = f·[k ≤ 10] + f·[k ≥ 11]: the low part E vanishes identically (Dirichlet coefficients of k ≤ 10 cancel, checked by `norm_num` + `ring` over 625 terms), and the high part has 625 terms, each in [0, 11^−n]. A real-inequality lemma `alg` assembles the bounds into the explicit constant 625 + 4K(22+K) + 5K for n ≥ 2. Mathlib's `zeta_nat_eq_tsum_of_gt_one` and `Complex.ofReal_tsum` connect ζ to the real series.

## Axioms
'OeisA114362.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-11-08. 2 compiles (1: clean apart from a `<;>` lint; 2: clean + axioms).
