# OeisA63880.exists_primitive_of_a

- Source: `FormalConjectures/OEIS/63880.lean:233` (category research solved)
- Statement: every n with σ(n) = 2·usigma(n) is m·s with m a primitive term, s squarefree, gcd(m, s) = 1.
- Verified file: `work/oeis63880.lean`. `results/oeis63880_exists_primitive.lean` is an identical hand copy, not compiled separately. The definitions (and `Set.IsPrimitive`) are restated locally, and the file uses targeted imports.

**Proof idea.** I proved that usigma is multiplicative (`U_mul`: the unitary divisors of ab are the products of the unitary divisors of a and of b, injective via gcd), and that usigma(p^j) = 1 + p^j. The ratio σ(p^j)/usigma(p^j) is ≥ 1, it is 1 for j ≤ 1, and it is strictly increasing in j (`pp_le`/`pp_lt`, via the geometric sum identity). So for d ∣ m: σ(d)·u(m) ≤ σ(m)·u(d) (`gen_le`, induction over prime-power/coprime decompositions). The inequality is strict if some prime has v_p(d) < v_p(m) and v_p(m) ≥ 2 (`gen_lt`). The main theorem uses strong induction on n. If some prime p divides n exactly once, then n/p ∈ A (by cancelling the factor p+1), and p is moved into s. Otherwise n is powerful, and any proper divisor d ∈ A would give the strict inequality, which contradicts σ = 2u on both sides. So n is primitive (s = 1).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-11-06
