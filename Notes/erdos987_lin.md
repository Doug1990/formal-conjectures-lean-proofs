# erdos987_lin

- Statements: `Erdos987.erdos_987.variants.linear_upper_bound_weak` (line 113), `Erdos987.erdos_987.variants.linear_upper_bound_clunie` (line 125), `Erdos987.erdos_987.variants.linear_upper_bound` (line 141)
- Source: `FormalConjectures/ErdosProblems/987.lean` (research solved, Clunie 1967)
- Lean file: `results/erdos987_lin.lean` (identical to `work/erdos987_lin.lean`)

## Proof idea
The witness is the van der Corput sequence v, defined by v(2q) = v(q)/2 and v(2q+1) = (v(q)+1)/2, with values in [0,1). Write F(t,n) = Σ_{j<n} e(t·v_j). Splitting by parity gives F(t,2q) = (1+e(t/2))·F(t/2,q). For odd k this gives F(k,2q) = 0, because e(k/2) = −1, so |F(k,n)| ≤ 1. For k = 2m it gives F(2m,2q) = 2F(m,q) and F(2m,2q+1) = F(m,q) + F(m,q+1). Strong induction on k then gives |F(k,n)| ≤ 2^{v₂(k)} ≤ k for every n. This directly gives `linear_upper_bound` (x_j = v_j ∈ [0,1), A_k ≤ k, even with sup over n instead of limsup). The shifted sequence x_j = v_{j+1} ∈ (0,1) has partial sums F(k,n+1) − 1, so its bound is k + 1 (`linear_upper_bound_clunie`). The weak 2k version uses a cruder bound 2k − 1 that is proved in the same way.

## Axioms
`[propext, Classical.choice, Quot.sound]` for all three theorems.

## Date
2026-11-13
