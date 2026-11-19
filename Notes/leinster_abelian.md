# LeinsterGroup.abelian_is_leinster_iff_cyclic_perfect

- Source: `FormalConjectures/Wikipedia/LeinsterGroup.lean:86` (category research solved)
- Statement: a finite abelian group is Leinster iff it is cyclic of perfect order.

Proof idea: for a cyclic group the normal subgroups correspond bijectively to divisors of n,
so the sum of their orders is σ(n) (lemma `sum_cyclic`, generalised from the earlier
`cyclic_of_perfect_is_leinster` proof); this gives "cyclic ⇒ (Leinster ⇔ perfect)". If G is
abelian but not cyclic, all subgroups are normal; the cyclic subgroups ⟨g⟩ have orders summing
to more than n (each element generates exactly one of them, fibre ⊆ subgroup, and the fibre of
⟨g₀⟩ for g₀ ≠ 1 misses 1), and ⊤ is not among them, so the total exceeds 2n — never Leinster.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-31. Compiles: 3 (1: missing `Mathlib.Data.SetLike.Fintype` for the
`Fintype (Subgroup G)` instance; 2: `set` did not rewrite a later `have`; 3: clean + axioms).
