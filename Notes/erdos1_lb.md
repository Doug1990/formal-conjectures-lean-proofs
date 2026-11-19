# Erdos1.erdos_1.variants.lb

- Source: `FormalConjectures/ErdosProblems/1.lean:90` (category research solved, Erdős–Moser 1956)
- Statement: there is o = o(1) such that every sum-distinct set A ⊆ {1..N} with |A| = n satisfies (1/4 − o(n))·2ⁿ/√n ≤ N.
- Imports: targeted Mathlib imports instead of `FormalConjecturesUtil`. `IsSumDistinctSet` is restated word for word, and the `@[category]` attribute is dropped.

## Proof idea
This is the second-moment (Chebyshev) argument. Write T = Σ_{a∈A} a and s_S = Σ_{a∈S} a. By induction on A, Σ_{S⊆A} (2s_S − T)² = 2ⁿ Σ a² ≤ 2ⁿ·n·N² (lemma `sq_sum`). Set L = 2√n·N. Each subset with |2s_S − T| ≥ L contributes at least L² = 4nN² to the sum, so at most 2ⁿ/4 subsets are like that. The other subsets have pairwise distinct sums s_S (sum-distinctness), and all of these sums lie in an interval of length < L. So there are at most L + 1 of them (lemma `card_le_of_close`, via min'/max'). Hence (3/4)·2ⁿ ≤ 2√n·N + 1 (lemma `key`). This already gives the claim with o ≡ 0 for n ≥ 2. For n = 1 it follows from N ≥ 1, and for n = 0 it is trivial because √0 = 0 makes the left side 0. The argument actually gives the constant 3/8 > 1/4.

## Axioms
`'Erdos1.erdos_1.variants.lb' depends on axioms: [propext, Classical.choice, Quot.sound]`

The only compiler message is an unused-variable lint on the binder name `h` inside the original statement, which may not be changed.

Date: 2026-10-31. 3 compiles.
