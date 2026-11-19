# Erdos1199.erdos_1199.variants.three

- Source: `FormalConjectures/ErdosProblems/1199.lean:53` (category research solved, Hindman 1979)
- Statement: there is a 3-colouring of ℕ such that for every infinite A ⊆ ℕ, the sumset A+A is not monochromatic.

**Proof idea.** Colour n by ⌊(3/2)·log₂ n⌋ mod 3 (as an element of ZMod 3 = Fin 3). Pick any a ∈ A and some b ∈ A with b > 4a. Then log₂(2b) = 1 + log₂ b and log₂ b ≤ log₂(a+b) < log₂ b + 1/3, because (a+b)³ < (5b/4)³ < 2b³. So the two arguments t₁ = (3/2)log₂(a+b) and t₂ = (3/2)log₂(2b) satisfy 1 < t₂ − t₁ ≤ 3/2. Their floors therefore differ by 1 or 2, which is not 0 mod 3, so a+b and b+b get different colours. This is a self-contained argument; it does not reconstruct Hindman's original colouring.

- Axioms: `propext, Classical.choice, Quot.sound`
- Compiles: 2 (1: clean; 2: clean + `#print axioms`)
- Date: 2026-11-08
