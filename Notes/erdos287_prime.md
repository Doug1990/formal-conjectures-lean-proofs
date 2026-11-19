# Erdos287.erdos_287.variants.prime_conjecture_implies

- Source: `FormalConjectures/ErdosProblems/287.lean:108` (category textbook)
- Statement: the hypothesis `type_of% erdos_287.variants.prime_conjecture` is spelled out literally
  (∃ N₀, ∀ N ≥ N₀, ∃ prime p ∈ [N, 2N] with (p+1)/2 prime); the rest of the statement is unchanged.
  `max_gap` is restated verbatim from the source file. Targeted imports, no FormalConjecturesUtil.

## Proof idea

Take k₀ = 2N₀ + 100 and assume a representation 1 = Σ 1/n_i (n_1 < … < n_k, n_1 ≥ 2) with all
gaps ≤ 2. Write a = n_1, b = n_k. Then b ≥ a + k − 1. If b ≤ 2a + 1, then a ≥ 98 and the terms
lie in [a, 2a+1], whose reciprocal sum is ≤ 1/a + 5/6 < 1 (lemma `tail_le`: Σ_{i<m+2} 1/(m+2+i)
≤ 5/6, shown by induction). So b ≥ 2a + 2. Apply the prime hypothesis with N = ⌊b/2⌋ to get a prime
p ∈ (a, b] with q = (p+1)/2 prime. If p is a term, use r = p. If not, the gap bound forces p − 1 and
p + 1 = 2q to be terms, and we use r = q. In both cases r ≥ 13, r divides some term, and every term
is < 4r. The lemma `key` then gives a contradiction. Multiply Σ 1/n_i = 1 by r·6·∏_{r∤n_i} n_i. Reduce
mod r. You get r | P·Σ_{r|n_i} 6/(n_i/r) with r ∤ P. The last sum is a nonempty subset sum of
{6, 3, 2}, so it lies in [2, 11] and is not divisible by r.

Axioms: `propext, Classical.choice, Quot.sound`

Compiles: 3 (1: higher-order unification failure in `Finset.sum_image`, fixed with `rw`; 2: clean;
3: + `#print axioms`). The only remaining warning is the unused-variable lint on the statement's own
binder `hk₀`.

Date: 2026-11-01
