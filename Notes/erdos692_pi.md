# erdos692_pi

- Statement: `Erdos692.erdos_692.parts.i` (δ₁(n, ·) is not unimodular on (n+1, ∞) for every n), plus a second copy of `erdos_692.variants.cambie_three`
- Source: `FormalConjectures/ErdosProblems/692.lean:71` (category research solved, Cambie; answer "no")
- Date: 2026-11-17

## Proof idea
Every δ₁(a, b) exists: the set is b!-periodic, because each d ∈ (a, b) divides b!. So δ(a, b) := cnt(a, b, b!)/b! satisfies the hypothesis `∀ a b, IsDelta₁ a b (δ a b)` (lemma delta_all, via delta_has = periodic density). Apply the assumed universal statement at n = 3 to get M > 4 with δ(3, ·) monotone on (4, M] and antitone on [M, ∞). By `cambie_three` (proved in the same file: periodic densities 7/20, 1/3, 38/105 by kernel decide), δ(3,7) < δ(3,6) and δ(3,7) < δ(3,8). If M ≤ 7, antitonicity on 7 ≤ 8 contradicts δ(3,7) < δ(3,8). If M ≥ 8, monotonicity on 6 ≤ 7 contradicts δ(3,7) < δ(3,6). `UnimodularOn` and `HasDensity` are restated locally with the checkout's definitions.

## Axioms
`'Erdos692.erdos_692.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]`
`'Erdos692.erdos_692.variants.cambie_three' depends on axioms: [propext, Classical.choice, Quot.sound]`
