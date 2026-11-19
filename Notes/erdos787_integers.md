# erdos787_integers

- Statement: `Erdos787.erdos_787.variants.integers` (g ℤ n = g ℝ n, Choi's observation), checkout file `FormalConjectures/ErdosProblems/787.lean:105`, category research solved.
- Date: 2026-11-12

## Proof idea
The two sets of admissible m are shown to be equal, so their sSup agree and no boundedness argument is needed. The key lemma `IZ.pull` says the following. Suppose e is injective on A and satisfies e(x+y) = e x + e y whenever x, y, x+y ∈ A. Then a good subset B' of e(A) pulls back to the good subset A ∩ e⁻¹(B'), which has at least as many elements. For ℤ → ℝ, take e to be the cast. For ℝ → ℤ, choose a ℚ-linear functional f : ℝ → ℚ that is nonzero on every difference a − b of distinct elements of A (`IZ.sep`). It is built by induction: f + q·g with q chosen outside a finite bad set, and g from `Module.Projective.exists_dual_ne_zero`. Then multiply by a common denominator d of f(A) (`IZ.common`) and take e(a) = the integer d·f(a). The definitions `g` and `disjoint_restrictedSumset_iff` are copied verbatim from the checkout, and `Finset.restrictedSumset` is a local copy.

## Axioms
'Erdos787.erdos_787.variants.integers' depends on axioms: [propext, Classical.choice, Quot.sound]
