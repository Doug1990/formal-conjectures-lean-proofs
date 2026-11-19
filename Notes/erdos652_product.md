# Erdos652.erdos_652.variants.product

- Source: `FormalConjectures/ErdosProblems/652.lean:83` (category research solved)
- Statement: `∃ c > 0, ∀ points p q, p ∈ points → q ∈ points → p ≠ q → c * #points ≤ R(p) * R(q)`, where R = `distinctDistancesFrom`
- Date: 2026-11-10

**Proof idea.** Take c = 1/4. Map every point x of `points \ {p, q}` to the pair (dist x p, dist x q). This pair lies in D_p × D_q, so there are at most R(p)·R(q) values. Each fibre lies on two circles with distinct centres, so it has at most 2 points (Mathlib `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`, with finrank ℝ² = 2). Hence n − 2 ≤ 2R(p)R(q). Since R(p), R(q) ≥ 1 (q is at some distance from p, and vice versa), n ≤ 4R(p)R(q). `distinctDistancesFrom` is restated locally. Its `open Classical` DecidableEq is bridged to the `WithLp` instance by `dDF_eq` (`congr 2; ext; simp only [Finset.mem_erase]`).

Axioms: `[propext, Classical.choice, Quot.sound]`
