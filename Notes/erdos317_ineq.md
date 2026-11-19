# Erdos317.claim2_inequality

- Source: `FormalConjectures/ErdosProblems/317.lean:60` (category textbook)
- Statement: eventually in n, for δ : Fin n → {-1,0,1}, if S = Σ δ_k/(k+1) ≠ 0 then |S| ≥ 1/lcm(1..n).

Proof idea: holds for every n. With L = lcm(1..n) > 0, each k+1 ∣ L, so L·δ_k/(k+1) = δ_k·(L/(k+1)) is an integer; hence L·S = z ∈ ℤ, z ≠ 0 because S ≠ 0, so 1 ≤ |z| = L·|S|.

Axioms: `'Erdos317.claim2_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30
