# Erdos12.isGood_example

- Source: `FormalConjectures/ErdosProblems/12.lean:45` (category textbook)
- Statement: `IsGood {p ^ 2 | (p : ℕ) (_ : p ≡ 3 [MOD 4]) (_ : p.Prime)}`.

Proof idea: the set is infinite because Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`
with the unit 3 ∈ ZMod 4) gives arbitrarily large primes p ≡ 3 mod 4, and p ≤ p². For the
"good" condition, suppose p² ∣ q² + r² with p² < q². Then p ∣ q² + r² in ZMod p. If q ≢ 0, then
q² = −r² makes −1 a square, which `ZMod.mod_four_ne_three_of_sq_eq_neg_sq` excludes for
p ≡ 3 mod 4. So p ∣ q, hence p = q since both are prime, which contradicts p² < q². The divisibility
premise is therefore never satisfied, which is the intended mathematical content (the source cites
a proof by AlphaProof). The `abbrev IsGood` is restated locally, with targeted imports.

Axioms: `'Erdos12.isGood_example' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-30. Compiles: 2 (1: `isUnit_of_mul_eq_one` unknown → explicit `Units` term).
