# casas_char_p

- Statement: `CasasAlvero.casas_alvero.positive_char_counterexample` (category research solved, Graf von Bothmer–Labs–Schicho–van de Woestijne)
- Source: `FormalConjectures/Paper/CasasAlvero.lean:161` in google-deepmind/formal-conjectures
- Statement: for a prime p there is a field K of characteristic p in which P = X^(p+1) − X^p is monic, has the Casas-Alvero property, and is not of the form (X − α)^deg P.

## Proof idea

Generic over any field K with CharP K p. P has natDegree p+1 and is monic. The Hasse derivatives are explicit: D^i P = C(p+1,i)·X^(p+1−i) − C(p,i)·X^(p−i) (from `hasseDeriv_monomial`). For i < p both exponents are positive, so 0 is a common root of P and D^i P. For i = p, D^p P evaluated at 1 is (p+1) − 1 = p = 0 in K, and P(1) = 0. So the root version of the property holds, and that implies the coprimality version (the file's API lemma, restated). If P = (X − α)^(p+1), evaluating at 0 forces α = 0, and then evaluating at 1 gives 0 = 1. The witness is K = ULift (ZMod p), so that it fits the universe-polymorphic `Type*` in the statement.

## Axioms

`'CasasAlvero.casas_alvero.positive_char_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]`

## Date

2026-11-01 (2 compiles; definitions restated, targeted imports)
