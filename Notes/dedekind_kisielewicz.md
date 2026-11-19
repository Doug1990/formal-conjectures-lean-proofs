# DedekindNumber.M_eq_kisielewiczFormula

- Source: `FormalConjectures/Wikipedia/DedekindNumber.lean:259` (category research solved, Kisielewicz 1988)
- Statement (unchanged): `theorem M_eq_kisielewiczFormula : M = kisielewiczFormula`
- File: `results/dedekind_kisielewicz.lean` (the definitions `M`, `M'`, `IsSperner`, `kisielewiczFormula` and the upstream proof of `M_eq_M'` are copied from the source file; the only change to a copied helper proof is `Set.toFinite _` instead of `Set.finite_iff_bddAbove` in `exists_minimal_true_subset`, to avoid an extra import).

## Proof idea
Every inner factor `1 - b_m^i + b_m^i b_m^j` is 0/1 and the product over `m ≤ log2 i` is the indicator of "bits of i ⊆ bits of j" (bits of i above log2 i vanish). Hence each summand for `k` is the indicator of AC(k): no two bits i < j of k with bitset(i) ⊆ bitset(j); the j = 2^n row is harmless because k < 2^(2^n). So the formula counts `k < 2^(2^n)` satisfying AC. Encode `s ⊆ Fin n` as `enc s = Σ 2^x` and a family A as `Enc A = Σ_{s∈A} 2^(enc s)`. Using `Finset.toFinset_bitIndices_sum_two_pow`, the bits of `enc s` are exactly s and the bits of `Enc A` are exactly the codes of A, so `Enc` is a bijection from families to `[0, 2^(2^n))` with inverse `Dec k = {s | testBit k (enc s)}`. Since `s ⊂ t ⇒ enc s < enc t`, AC(Enc A) ↔ A is Sperner. That gives M' n = formula n, and the upstream `M_eq_M'` finishes the proof.

## Axioms
`'DedekindNumber.M_eq_kisielewiczFormula' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-31. Compiles: 5 (1: missing `Mathlib.Tactic.GeneralizeProofs` olean; 2: `Set.exists_min_image` import; 3: missing LocallyFiniteOrder on Finset; 4: clean; 5: + axioms).
