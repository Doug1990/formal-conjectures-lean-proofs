# erdos1191_liminf

- Statement: `Erdos1191.erdos_1191.variants.liminf_le` (category research solved, Erdős; see Halberstam–Roth)
- Source: `FormalConjectures/ErdosProblems/1191.lean` (line 68) in google-deepmind/formal-conjectures
- Same mathematics as `Erdos158.erdos_158.variants.isSidon'` (`FormalConjectures/ErdosProblems/158.lean:67`), but stated with `Iio N` and `< ⊤`. That version is NOT proved here.

## Proof idea
We take c = e^8 and argue by contradiction. Suppose A(x)·√(log x) > c√x for all x ≥ x0, where A(x) = |A ∩ [1,x]|. Pick X with K = A(X) ≥ x0 + 2 and split [1,X] into blocks of length M = K, with n_s elements in block s. A Sidon set has pairwise distinct differences, so two pairs in the same block are counted at most 2M times, which gives Σ n_s² ≤ K + 2M. Weighted Cauchy–Schwarz with weights 1/√(s+1), together with harmonic(X) ≤ 1 + log X, gives K·G² ≤ 6K(1 + log X), where G = Σ_{a∈A, K<a≤X} a^{-1/2}. Induction on X gives c·(H_K − H_{A(K)}) ≤ √(log X)·G, where H is the harmonic number. The trivial Sidon bound A(K)² ≤ A(K) + 2K + 2 gives A(K) ≤ 3√K, and the hypothesis at X gives log K ≥ 8 + (log X)/4. Together these give H_K − H_{A(K)} ≥ 1 + (log X)/8, so 625(1 + L/8)² ≤ 6L(1 + L) with L = log X > 0. That is impossible.

## Axioms
'Erdos1191.erdos_1191.variants.liminf_le' depends on axioms: [propext, Classical.choice, Quot.sound]

## Date
2026-11-13
