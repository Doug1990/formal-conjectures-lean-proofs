# firstproof4_two

- Statement: `Arxiv.«2602.05192».four_2` (category research solved), the n = 2 case of First Proof Problem 4.
- Source: `FormalConjectures/Arxiv/2602.05192/FirstProof4.lean:166`
- Date: 2026-11-02
- Compiles: 2 (1st passed with an unused-simp-arg lint only, 2nd clean + axioms)

## Proof idea
A monic degree-2 real polynomial with 2 roots splits as (X−a)(X−b) (`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`). For such a polynomial, 1/Φ = (a−b)²/2. If a = b, the roots are not nodup, so Φ = ⊤ and both sides are 0. Otherwise Φ = 2/(a−b)². The convolution ⊞₂ has explicit coefficients (lemma `conv2`): 1, a₁+b₁, a₀+b₀+a₁b₁/2. Its discriminant is therefore (a−b)² + (c−d)² ≥ 0, so it factors as (X−t₁)(X−t₂) with t = (S ± √Δ)/2. Hence 1/Φ(p ⊞₂ q) = 1/Φ(p) + 1/Φ(q): for n = 2 the inequality holds with equality. Definitions are restated locally, unchanged.

## Axioms
'Arxiv.«2602.05192».four_2' depends on axioms: [propext, Classical.choice, Quot.sound]
