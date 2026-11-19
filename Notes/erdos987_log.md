# Erdős 987: log_lower_bound and parts.i

- Statements: `Erdos987.erdos_987.variants.log_lower_bound` (ErdosProblems/987.lean:93) and `Erdos987.erdos_987.parts.i` (ErdosProblems/987.lean:73), both tagged `research solved`.
- Source file: `formal-conjectures/FormalConjectures/ErdosProblems/987.lean`. `A` and `e` are restated locally, and the file uses targeted imports.

**Proof idea.** We take c = 1 and argue by contradiction. Suppose A_k < log k for all k ≥ K0, and set K = K0 + 1. Pick s = ⌈log K⌉ + 19 and L = s⁴. For each of the finitely many frequencies K·m with 1 ≤ m < L², the partial sums S_n(K m) eventually stay below log(K m) in absolute value. Fix one N that works for all of them. Then take the L points t_j = K·x_{N+j} for j < L. The block sum Σ_j e(m t_j) equals S_{N+L}(Km) − S_N(Km), so its absolute value is less than 2 log(K L²). The Fejér/large-sieve identity (`SL.ident`) applies in the version `SL.core'`, which needs the bound only for 0 < m < L². It gives L ≤ 1 + 4 log²(K L²). With log(K L²) ≤ 9s this contradicts L = s⁴ for s ≥ 19. Taking multiples of K avoids the small frequencies, where A_k may be ⊤. `parts.i` then follows: log k → ∞, so A_k ≥ b + 1 for infinitely many k and every real b, and `le_limsup_of_frequently_le` gives limsup = ⊤.

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-13
