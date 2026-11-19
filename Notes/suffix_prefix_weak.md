# suffix_prefix_weak

- Statement: `SuffixPrefixAvoidance.suffix_prefix_avoidance_weaker_bound` (category research solved)
- Source: `FormalConjectures/Other/SuffixPrefixAvoidance.lean:90`
- Date: 2026-11-02
- Compiles: 3 (1: Finset→Set coercion in the InjOn statement; 2: unused simp-arg lint only; 3: clean + axioms)

## Proof idea
For each shift k ∈ [0, n), map (a, b) ∈ A × B to `rot k a b`, the cyclic left shift by k of the
length-2n word `a ++ b`. Each such map is injective (`rot_inj`). Images for different shifts
k < k′ are disjoint (`rot_disj`): if `rot k a b = rot k′ a′ b′`, comparing positions
n − k′ + t for t < d = k′ − k shows that the last d letters of a equal the first d letters of b′.
That contradicts suffix-prefix avoidance at index d − 1. So the map (k, a, b) ↦ rot k a b is
injective on [0,n) × A × B, giving n·|A|·|B| ≤ q^(2n), and the claim follows by casting to ℚ.
The definitions are restated locally with targeted imports. The statement is unchanged.

## Axioms
`'SuffixPrefixAvoidance.suffix_prefix_avoidance_weaker_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
