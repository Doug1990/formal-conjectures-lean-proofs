# erdos878_limsup

- Statement: `Erdos878.erdos_878.variants.H_div_self_limsup_infinite` (research solved, Erdős [Er84e])
- Source: `FormalConjectures/ErdosProblems/878.lean:150`
- Date: 2026-11-14

Proof idea. H(x) = Σ_{n<x} Σ_{p|n} p^{⌊log_p n⌋}/n. After swapping the sums, H(x) ≥ Σ_{p∈P} Σ_{n<x, p|n} p^{⌊log_p n⌋}/n for any finite set P of primes. Given C, choose N such that Σ_{p<N prime} 1/p ≥ 16(|C|+1) (divergence of Σ1/p, `not_summable_one_div_on_primes`). A pigeonhole Dirichlet step (LS.dir, M buckets) gives an arbitrarily large integer k such that k/log p lies within 1/M of an integer j_p for every prime p < N, with M ≥ 2 log N. Then |k − j_p log p| < 1/2, and for x = ⌈4e^k⌉ this gives 2p^{j_p} ≤ x ≤ 8p^{j_p} (using e^{1/2} < 2). The p^{j−1} multiples of p in [p^j, 2p^j) have ⌊log_p n⌋ = j, so each term is ≥ 1/2, and the contribution of p is ≥ p^{j−1}/2 ≥ x/(16p). Summing over p gives H(x) ≥ (x/16)Σ1/p ≥ Cx.

Axioms: `propext, Classical.choice, Quot.sound`
