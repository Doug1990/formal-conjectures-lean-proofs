# Erdos338.erdos_338.variants.bateman

- Source: `FormalConjectures/ErdosProblems/338.lean:148` (category research solved, Bateman's observation)
- Date: 2026-11-10
- Verified file: `work/erdos338_bateman.lean` (results copy is identical). Defs `HasOrder`, `HasRestrictedOrder`, `basisOrder`, `restrictedOrder` are restated verbatim from the source; targeted imports replace FormalConjecturesUtil.

Proof idea: A = {1} ∪ {x > 0 : h ∣ x}. Every multiset of elements of A splits into n₁ ones and a part with sum h·e, and that part is nonempty when e ≠ 0 (`Bat.split`). Order ≤ h: write m = h·⌊m/h⌋ + (m mod h), which needs at most (m mod h) ones plus one multiple. Order ≥ h: m = h(M+1) + (h−1) forces e ≤ M+1 and n₁ ≥ h−1. Either e = 0 (then n₁ ≥ h) or there is at least one extra summand, so there are ≥ h summands. No restricted order: a set of distinct elements contains 1 at most once, so its sum is ≡ 0 or 1 mod h, and h(M+1)+2 ≡ 2 is never reached (h ≥ 3).

Axioms: `'Erdos338.erdos_338.variants.bateman' depends on axioms: [propext, Classical.choice, Quot.sound]`
