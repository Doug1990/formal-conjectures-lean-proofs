# Erdos454.erdos_454.variants.two_le_limsup

- Source: `FormalConjectures/ErdosProblems/454.lean:45` (category research solved, Pomerance 1979)
- Statement: `2 ≤ limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop`, where
  `f n = min_{0<i<n} (p_{n+i} + p_{n-i})`.
- Verified file: `work/erdos454_two.lean` (this file is an identical copy).

Proof idea: primes grow faster than any linear function (`growth`: `s·k ≤ p_k + C`),
by a sieve with the primes below b, where ∏(1−1/p) ≤ 1/(s+1) (divergence of Σ1/p;
helpers copied from results/erdos673_i.lean). For slope s = p_M (M = max N 2), the
integer function g(k) = p_k − s·k is bounded below and tends to infinity, so it has a
largest minimiser n, and n ≥ M because g(M) < g(k) for every k < M. (n, p_n) is then an
exposed point of the lower convex hull. So g(n+i) > g(n) and g(n−i) ≥ g(n), which gives
p_{n+i} + p_{n−i} > 2p_n. All three primes are odd, so the gap is at least 2. That holds
for infinitely many n, and `le_limsup_of_frequently_le'` finishes the proof.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-08 (1 compile with errors, 1 clean compile + axioms)
