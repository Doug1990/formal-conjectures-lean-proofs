# erdos723_pp

- Statement: `Erdos723.erdos_723.variants.prime_power_is_projplane_order` (research solved)
- Source: `FormalConjectures/ErdosProblems/723.lean:45`
- Date: 2026-11-14

Proof idea: for n = p^k, take K = GaloisField p k (|K| = p^k by `GaloisField.card`). The points and lines are both ℙ K (Fin 3 → K), with incidence given by orthogonality. Mathlib already provides the `ProjectivePlane` instance (`Configuration.ofField`). Its order o satisfies |ℙ| = o² + o + 1 (`ProjectivePlane.card_points`). `Projectivization.card_of_finrank` gives |ℙ| = 1 + q + q², and since o ↦ o² + o + 1 is injective, o = q. The imports are Mathlib-only; the statement is copied verbatim.

Axioms: `[propext, Classical.choice, Quot.sound]`
