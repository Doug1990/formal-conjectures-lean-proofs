# firstproof4_three

- Statement: `Arxiv.«2602.05192».four_3` (research solved, n = 3 case of First Proof Theorem 4)
- Source: `FormalConjectures/Arxiv/2602.05192/FirstProof4.lean:175` in the checkout
- Date: 2026-11-02

## Proof idea

For a monic cubic with coefficients (1, c₂, c₁, c₀), the shift invariants A = c₁ − c₂²/3 and
B = c₀ − c₂c₁/3 + 2c₂³/27 are additive under ⊞₃ (checked from the explicit coefficient form of
⊞₃, `conv3`). When p = (X−a)(X−b)(X−c), a direct computation gives 1/Φ(p) =
2((a−b)(b−c)(c−a))²/((a−b)²+(b−c)²+(c−a)²)² = (−4A³−27B²)/(18A²). Here A = −Σ(a−b)²/6 ≤ 0, and
in the multiple-root case both sides are 0 (`phi_cubic`, `inv_phi3`). For A < 0 this equals
−2A/9 − (3/2)(B/A)². Since (B₁+B₂)/(A₁+A₂) is a convex combination of B₁/A₁ and B₂/A₂, the
superadditivity follows (`conv_ineq`, `key_ineq`). For the convolution g there are three cases.
If g has 3 real roots counted with multiplicity, the same formula applies. Exactly 2 is
impossible for a real monic cubic (`card_ne_two`). If it has at most 1, then Φ(g) = 0 and
1/Φ(g) = ⊤.

## Axioms

`'Arxiv.«2602.05192».four_3' depends on axioms: [propext, Classical.choice, Quot.sound]`

Defs (convolution, Φ, FourProp) are restated locally with targeted Mathlib imports. The
statement is unchanged.
