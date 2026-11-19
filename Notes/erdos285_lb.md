# Erdos285.erdos_285.variants.lb

Source: FormalConjectures/ErdosProblems/285.lean:67 (category research solved).

Proof idea: let N = n_k be the last term of a strictly increasing sequence n_0 < … < n_k of positive integers whose reciprocals sum to 1. Strict monotonicity gives n_i ≤ (N−k)+i, so 1 = Σ 1/n_i ≥ Σ_{i≤k} 1/(m+i) with m = N−k ≥ 1. This sum is at least log(N+1) − log m (telescoping with log(1+1/j) ≤ 1/j). Hence N+1 ≤ e·m = e(N−k), i.e. e·k + 1 ≤ (e−1)N. Take o(k) = −1/(k+1), which tends to 0. Then (1+o(k))·e/(e−1)·(k+1) = e·k/(e−1) ≤ N = f(k), using only that f(k) belongs to the set (the first component of IsLeast).

Axioms: propext, Classical.choice, Quot.sound

Compile: clean apart from an unused-variable lint on `hS`, which is part of the original statement.

Date: 2026-11-10
