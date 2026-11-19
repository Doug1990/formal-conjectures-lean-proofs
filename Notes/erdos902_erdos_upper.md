# Erdos902.erdos_902.variants.erdos_upper

- Source: FormalConjectures/ErdosProblems/902.lean:151 (category research solved, Erdős 1963)
- Statement: ∀ ε > 0, eventually f(n) ≤ (log 2 + ε) n² 2ⁿ.
- Verified file: work/erdos902_up.lean (compiled 2026-11-05, 2 compiles). The proof is in
  results/erdos902_erdos_upper.lean, which is the same text as the verified work file.

Proof idea: this is Erdős's random-tournament argument, done as an exact count. `F3.exists_of`
reuses the counting lemmas from erdos_lower (bad_count + union bound). It shows that if
C(m,n)(2ⁿ−1)^{m−n} < 2^{n(m−n)}, then some tournament on Fin m has property S_n, so f(n) ≤ m.
`F4.ineq_nat` derives this from the real inequality n·log m < (m−n)/2ⁿ, using C(m,n) ≤ mⁿ and
(1−2⁻ⁿ)^k ≤ exp(−k/2ⁿ). The proof takes m = ⌊(log 2+ε)n²2ⁿ⌋. Then log m ≤ log c + 2 log n + n log 2
and (m−n)/2ⁿ ≥ c n² − 1, so the condition reduces to n log c + 2n log n + 1 < ε n². That holds
eventually because log n / n → 0 (`Real.tendsto_pow_log_div_mul_add_atTop`).

Axioms: propext, Classical.choice, Quot.sound

Date: 2026-11-05
