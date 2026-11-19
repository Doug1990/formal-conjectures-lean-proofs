# LeinsterGroup.exists_nonabelian_leinster_group

- Source: `FormalConjectures/Wikipedia/LeinsterGroup.lean:98` (category research solved)
- Statement: there is a finite group `G` that is Leinster (the orders of its normal subgroups add up to `2·|G|`) and is not abelian.

## Proof idea
The witness is S₃ × C₅ = `DihedralGroup 3 × Multiplicative (ZMod 5)`, which has order 30. The general lemma `decomp` says that when |A| and |B| are coprime, every subgroup H of A × B equals (H ∩ A) × (H ∩ B). The reason is that for (a,b) ∈ H, the power (a,b)^(|B|·gcdB) equals (a,1) by Bézout. From this, `normalEquiv` gives a bijection between normal subgroups of A × B and pairs of normal subgroups of A and B, and `sum_prod` shows the Leinster sum is multiplicative. For D₃ the sum is 2·3 + σ(3) = 10 (`sum_odd`, reused from leinster_dihedral). For the cyclic C₅ it is σ(5) = 6 (`sum_cyclic`, reused from leinster_abelian). So the sum is 10·6 = 60 = 2·30, and `decide` checks this final arithmetic. Non-commutativity is checked with `decide` on (sr 0, 1) and (r 1, 1).

Reusable: `decomp`, `normalEquiv`, `sum_prod` (Leinster sum of a coprime direct product).

## Axioms
`'LeinsterGroup.exists_nonabelian_leinster_group' depends on axioms: [propext, Classical.choice, Quot.sound]`

The only remaining compile warning is an unused-section-variable lint on `sum_prod`.

Date: 2026-10-31
