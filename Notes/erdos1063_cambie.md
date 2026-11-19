# Erdős 1063: Cambie and Monier upper bounds

- Statements: `Erdos1063.erdos_1063.variants.cambie_upper_bound` (n_k ≤ k·lcm(1..k−1), k ≥ 3) and
  `Erdos1063.erdos_1063.variants.monier_upper_bound` (n_k ≤ k!, k ≥ 3), both `research solved`.
- Source: `FormalConjectures/ErdosProblems/1063.lean` (lines 143 and 158) in the checkout.
- Date: 2026-11-03.

## Proof idea
Let L be any number divisible by 1, …, k−1, L ≥ 2, and N = kL. Every j in [1, k−1] divides N, so
N − j = j·(N/j − 1), and N/j is a multiple of k. Hence k!·C(N,k) = N·(k−1)!·P with
P = ∏_{j=1}^{k−1}(N/j − 1), i.e. C(N,k) = L·P. For 1 ≤ i < k, N − i = i·(N/i − 1) divides L·P,
because i ∣ L and (N/i − 1) is a factor of P. N itself does not divide C(N,k): that would force
k ∣ P, but each factor N/j − 1 ≡ −1 (mod k) is coprime to k. So N lies in the defining set
(with exceptional index i0 = 0) and n_k ≤ N. Cambie takes L = lcm(1..k−1). Monier follows since
lcm(1..k−1) ∣ (k−1)!, so k·lcm ≤ k!.

## Axioms
`propext, Classical.choice, Quot.sound` (both theorems)
