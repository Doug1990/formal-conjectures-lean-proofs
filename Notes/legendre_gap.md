# LegendreConjecture.bounded_gap_legendre

- Source: FormalConjectures/Wikipedia/LegendreConjecture.lean:50 (category research solved, conditional statement; the checkout links an external AlphaProof proof)
- Statement: if p_{n+1} − p_n < p_n^(1/2 − c) eventually for some c > 0, then (n², (n+1)²) contains a prime for all large n.

Proof idea: pick N0 from the hypothesis and take n ≥ max(2, p_{N0}). Let k be the least index with
n² < p_k (exists because nth prime is strictly monotone, so p_k ≥ k). Then k = j+1, p_j ≤ n², and
j ≥ N0 because p_{N0} ≤ n ≤ n². The gap hypothesis gives
p_{j+1} − p_j < p_j^(1/2−c) ≤ p_j^(1/2) = √p_j ≤ √(n²) = n (lemma gap_le), so
n² < p_k < n² + n < (n+1)². The hypothesis c > 0 is used only to have exponent ≤ 1/2.

Axioms: [propext, Classical.choice, Quot.sound]

Date: 2026-10-31
