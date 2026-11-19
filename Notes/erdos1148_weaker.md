# Erdos1148.erdos_1148.variants.weaker

- Source: FormalConjectures/ErdosProblems/1148.lean:94 (category research solved)
- Statement: every n is x² + y² − z² (ℕ subtraction) with x², y², z² ≤ n + 2√n.

Proof idea: let a = ⌊√n⌋ and n = a² + r with 0 ≤ r ≤ 2a. If r = 2t+1 is odd, take
(x, y, z) = (a, t+1, t). If r = 0, take (a, 0, 0). If r = 4w+4, take (a, w+2, w). If
r ≡ 2 mod 4, write a = u + r/2 and take (a+1, u, u+1), so that x² = a² + 2a + 1 ≤ n + 2a.
In every case y, z ≤ a, and x² ≤ n + 2⌊√n⌋ ≤ n + 2√n (`Real.nat_sqrt_le_real_sqrt`).
The case work is done in ℕ with omega, treating squares as atoms after small `ring` identities.

Axioms: `'Erdos1148.erdos_1148.variants.weaker' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
