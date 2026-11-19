# Erdos83.erdos_83.variants.extremal

- Source: `FormalConjectures/ErdosProblems/83.lean:74` (category research solved)
- Statement: for every n there is a family F of 2n-subsets of Fin (4n) with pairwise intersections of size ≥ 2 and |F| = (C(4n,2n) − C(2n,n)²)/2.

**Proof idea.** F is the family of all 2n-subsets A with c(A) := |A ∩ [0,2n)| > n. Two such sets meet in at least 2 points
inside the first half, because |X ∪ Y| ≤ 2n and |X|, |Y| ≥ n+1. To count, split all 2n-subsets into c > n, c < n and c = n.
The half-swap involution σ(i) = i ± 2n gives c(σA) = 2n − c(A), so it is a bijection between the c > n and c < n classes.
The c = n class is in bijection with (n-subsets of the first half) × (n-subsets of the second half) via A ↦ (A ∩ L, A ∩ R),
so it has C(2n,n)² elements. Both halves have size 2n, which follows from c(univ) = 4n − c(univ). omega finishes the arithmetic.

- Axioms: `[propext, Classical.choice, Quot.sound]`
- Verified: 2026-11-08, 1 compile (work/erdos83_extremal.lean; results copy is identical)
