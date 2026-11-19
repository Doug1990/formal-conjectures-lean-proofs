# SidorenkoConjecture.sidorenko_conjecture.variants.path_blakley_roy

- Source: `FormalConjectures/Wikipedia/SidorenkoConjecture.lean:813` (category research solved, Blakley–Roy 1965)
- Statement: for every `n` and every finite nonempty host graph `G`,
  `t(K₂, G) ^ e(P_n) ≤ t(P_n, G)`.
- `homCount` / `homDensity` are restated locally (same definitions as
  FormalConjecturesForMathlib's HomDensity: `Fintype.card (H →g G)` divided by `|W|^|V|`).

## Proof idea
This is an entropy-style proof written as two log-Jensen inequalities, without measures. Let F_j = A^j·1
(the number of walks of length j from each vertex), d = the degrees, D = Σd, N = |W|. For a vertex v with
d(v) > 0, concavity of log gives d(v)·log F_{j+1}(v) ≥ d(v)·log d(v) + Σ_{u~v} log F_j(u). Summing over v and
using symmetry (stationarity of the degree measure) gives Σ_v d(v) log F_j(v) ≥ j·Σ d log d. The convexity of
x log x (via log y ≥ 1 − 1/y) gives Σ d log d ≥ D log(D/N). A second log-Jensen with weights d applied to
Σ_v F_{j+1}(v) = Σ_u d(u)F_j(u) then gives #walks of length j+1 ≥ D(D/N)^j = N(D/N)^{j+1}. Walks of length m
inject into homomorphisms P_{m+1} → G (via getVert), and e(P_{m+1}) ≥ m together with t(K₂,G) = D/N² ≤ 1
finishes the proof. The cases n = 0 and D = 0 are handled directly.
Reusable: `BR.jensen` (weighted log-AM-GM over a Finset), `BR.jensen_low`, `BR.main` (Blakley–Roy for any
symmetric nonnegative real matrix: N·(ΣA/N)^m ≤ 1ᵀA^m1), `BRG.card_le` (walks → path homs), `BRG.edges_ge`.

## Axioms
`'SidorenkoConjecture.sidorenko_conjecture.variants.path_blakley_roy' depends on axioms: [propext, Classical.choice, Quot.sound]`

Verified 2026-11-03, 3 compiles (work/sidorenko_path.lean).
