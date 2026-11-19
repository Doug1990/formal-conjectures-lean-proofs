# OeisA63880.exists_primitive_of_a

- Source: FormalConjectures/OEIS/63880.lean:233 (category research solved)
- Verified file: work/oeis63880_prim.lean. This result file is a hand copy of it, not compiled separately.
- Date: 2026-11-06

**Proof idea.** We use strong induction on n. If some prime p divides n exactly once, write n = k·p. Then A k holds by the file's `A_of_mul_prime`, and we append p to the squarefree part. Otherwise n is powerful, and we show that n itself is primitive. For a powerful m and any divisor d of m, we prove σ(d)·usigma(m) ≤ σ(m)·usigma(d), with strict inequality when d ≠ m (lemma `P.key`). This is an induction that peels off the prime power p^a of m.minFac. It uses multiplicativity of σ and a new lemma `usigma(m·p^a) = usigma(m)(1+p^a)`, which generalises the file's prime case. The local inequality σ(p^b)(1+p^a) < σ(p^a)·u(p,b) for b < a, a ≥ 2 comes from the geometric-sum identity S·p + 1 = S + p^(k+1) and a `linear_combination` computation in ℤ. If a proper divisor d were in A, we would have σ = 2·usigma at both d and m, which contradicts the strict inequality.

Axioms: `propext, Classical.choice, Quot.sound`

The file contains local restatements of `Set.IsPrimitive` and of the file's definitions, plus copies of the API lemmas it needs.
