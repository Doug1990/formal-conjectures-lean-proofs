# OeisA237271.observation_carmichael

- Source: FormalConjectures/OEIS/237271.lean:202 (category research solved)
- Statement: for every Carmichael number k, 3 ≤ a k.
- Proof idea: base b = 1 shows that k is composite and k > 1. Base b = k−1 is coprime to k, and if k were even (so k > 2), then k−1 ≡ −1 with odd exponent k−1 would give 1 = −1 in ZMod k, so k ∣ 2, a contradiction. Hence k is odd. Let D be the sorted divisor list. It has length ≥ 3 because {1, minFac k, k} are divisors, with D[0] = 1 and D[last] = k, and it is strictly increasing. Every divisor is odd. The first pair (1, D[1]) has D[1] ≥ 2. The last pair (D[n−2], k) has k = D[n−2]·m with m ≥ 2. These two are distinct entries of the zip, so the countP is ≥ 2 (helper `two_le_countP`), which gives a k ≥ 3.
- Axioms: propext, Classical.choice, Quot.sound
- Date: 2026-11-06 (2 compiles)
- `IsCarmichael` (FormalConjecturesForMathlib/NumberTheory/Carmichael.lean) and `a` are restated verbatim; targeted imports. results/*.lean is an identical copy of the verified work/oeis237271_carm.lean.
