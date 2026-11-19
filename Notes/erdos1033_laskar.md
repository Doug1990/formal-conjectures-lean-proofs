# erdos1033_laskar

- Statement: `Erdos1033.erdos_1033.variants.erdos_laskar` (research solved, Erdős–Laskar [ErLa85] / Fan [Fa88])
- Source: `FormalConjectures/ErdosProblems/1033.lean:91`
- Date: 2026-11-14

**Proof idea.** For n ≥ 100, let x = n/(2√3), h = ⌊x⌋, a = 2h, d = ⌈(7√3/6 − 2)n⌉ + 1. Vertices [0,h) = A₁, [h,2h) = A₂, [2h,n) = B. The graph is complete between A = A₁ ∪ A₂ and B. Inside A it is a d-regular circulant bipartite graph: x ∈ A₁ and y ∈ A₂ are adjacent iff (x+y) mod h < d. The map y ↦ (x+y) mod h is injective on any h consecutive integers, so the inner degree is exactly d. A-vertices have degree n−2h+d and B-vertices have degree 2h. B is independent and A is bipartite, so every triangle has exactly one vertex in B. Its degree sum is therefore 2(n−2h+d)+2h ≤ 2(√3−1)n + 6. The handshake lemma gives 4|E| = 8h(n−2h) + 4hd. This exceeds n² because 8x(n−2x) + 4x·(7−4√3)x = n² exactly (using √3² = 3), the rounding of h only helps since h ≥ n/4, and the +1 in d gives a positive linear surplus.

Axioms: `[propext, Classical.choice, Quot.sound]`
