# Erdos902.erdos_902.variants.erdos_lower

- Source: `FormalConjectures/ErdosProblems/902.lean:140` (category research solved, Erdős 1963), `2 ^ (n + 1) - 1 ≤ f n`.
- Verified file: `work/erdos902_low.lean` (clean + `#print axioms`). This results file is a hand copy and was not compiled separately.

**Proof idea.** There are two parts.

1. Lower bound for every S_n tournament (`F2.main`, as in `erdos902_f_two`). Use induction on n through the in-neighbourhood of a vertex: it has ≥ n−1 vertices and inherits S_{n−1}. Then the in-degree sum m(m−1)/2 gives m ≥ 2^(n+1) − 1.
2. Existence (`F3.exists_S`). This is needed because `f n` is an `sInf` and would be 0 if no S_n tournament existed. The proof is Erdős's counting argument. Tournaments on Fin m are encoded by σ : Fin m × Fin m → Bool. For a fixed n-set E, the σ in which E is undominated are counted exactly through the injective coordinate map (x, e) ↦ (min, max) (`count`, `countP`, `bad_count`): #Bad(E)·2^{n(m−n)} = (2^n − 1)^{m−n}·2^{m²}. The union bound then needs C(m,n)(2^n − 1)^{m−n} < 2^{n(m−n)}. That holds for m = n + t with t large, because C(m,n) ≤ (2t)^n and t^n/r^t → 0 for r = 2^n/(2^n − 1) > 1 (`tendsto_pow_const_div_const_pow_of_one_lt`).

The statement follows from `Nat.sInf_mem` and `F2.main`.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-05
