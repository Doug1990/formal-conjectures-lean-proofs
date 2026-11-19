# Kaplansky.promislow_group_is_torsionfree

- Source: `FormalConjectures/Wikipedia/Kaplansky.lean:100` (category API)
- Statement: `Monoid.IsTorsionFree PromislowGroup`, with PromislowGroup = ⟨a, b | b⁻¹a²ba², a⁻¹b²ab²⟩ (the Hantzsche–Wendt group).
  `Monoid.IsTorsionFree` (from FormalConjecturesForMathlib) is restated locally with the same definition.

Proof idea: put x = a², y = b², z = (ab)². From the two relators: b⁻¹xb = x⁻¹, a⁻¹ya = y⁻¹, then x, y commute,
(ab)²(ba)² = 1, so a and b both invert z, and x, y, z commute pairwise. Induction over left multiplication by
generators (`Subgroup.closure_induction_left`) gives a normal form g = x^i y^j z^k · s with s ∈ {1, a, b, ab}.
The relators hold for the affine maps α(v) = (v₀+1, 1−v₁, −v₂) and β(v) = (−v₀, v₁+1, 1−v₂) on ℤ³ (as
`Equiv.Perm (Fin 3 → ℤ)`), giving ψ : P →* Perm ℤ³. ψ(x^i y^j z^k) is the translation by (2i, 2j, −2k). For s ≠ 1,
ψ(g)² is a translation with an odd coordinate (2+4i, 2+4j or −2−4k). A translation of finite order is the identity,
so a finite-order g must have s = 1 and i = j = k = 0. No injectivity of ψ is needed.

Axioms: `'Kaplansky.promislow_group_is_torsionfree' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-02. 4 compiles: 3 on work/promislow.lean, then 1 on work/promislow_final.lean, which is this exact file.
The only remaining messages are 3 `<;>` style lints.
