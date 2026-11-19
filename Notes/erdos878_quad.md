# erdos878_quad

- Statement: `Erdos878.erdos_878.variants.H_lower_quadruple_log_infinitely_often` (research solved, Erdős Er84e)
- Source: `FormalConjectures/ErdosProblems/878.lean:170`
- Lean file: `results/erdos878_quad.lean` (an identical copy of `work/erdos878_quad.lean`)

## Proof idea
This is a quantitative version of the limsup proof (`results/erdos878_limsup.lean`), with c = 1/96. Given a, set N = a+16 and M = ⌈2 log N⌉+1. A quantitative simultaneous Dirichlet lemma (`LS.dirq`, pigeonhole over M^|S| buckets) gives k with a+3 ≤ k ≤ (a+4)·M^{π(N)} ≤ (3N)^{N+1} such that ‖k/log p‖ < 1/M for every prime p < N. Then x = ⌈4e^k⌉ satisfies 2p^j ≤ x ≤ 8p^j, so H(x) ≥ (x/16)·Σ_{p<N} 1/p. A Mertens-type lower bound (`QL.loglog_le`) gives log log N ≤ 2 Σ_{p<N} 1/p. It uses the Euler product over N-smooth numbers (`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`), the bound H_N ≥ log N and (1−1/p)⁻¹ ≤ e^{2/p}. On the other side, log x ≤ k+2 ≤ (3N)^{N+2}, and iterating the log gives log⁴ x ≤ 2 log 2 + log log N ≤ 3 log log N, since N ≥ 16 gives log log N ≥ 1.

## Axioms
`'Erdos878.erdos_878.variants.H_lower_quadruple_log_infinitely_often' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-14
