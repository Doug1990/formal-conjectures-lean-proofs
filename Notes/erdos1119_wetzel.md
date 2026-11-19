# erdos1119_wetzel

- Statements: `Erdos1119.erdos_1119.variants.easy_case` (line 91) and `Erdos1119.erdos_1119.variants.erdos_wetzel` (line 104)
- Source: `FormalConjectures/ErdosProblems/1119.lean` (both tagged `research solved`)
- File: `results/erdos1119_wetzel.lean` (identical to `work/erdos1119_wetzel.lean`)

Proof idea (Erdős [Er64g]): two distinct entire functions agree only on a countable set.
By the identity theorem (`AnalyticOnNhd.eq_of_frequently_eq`) the agreement set is discrete, and
discrete subsets of the hereditarily Lindelöf space ℂ are countable. Suppose #F > m with
ℵ₀ ≤ m and m⁺ < 𝔠. Pick G ⊆ F with #G = m⁺. The union of the agreement sets over the pairs
of distinct elements of G has cardinality ≤ m⁺·m⁺·ℵ₀ = m⁺ < 𝔠 = #ℂ, so some z₀ avoids it.
Then g ↦ g(z₀) is injective on G, so m⁺ ≤ #{f(z₀)} ≤ m, a contradiction. `easy_case` is the
case m > ℵ₀. `erdos_wetzel` is the case m = ℵ₀ (succ ℵ₀ = ℵ₁). There the hypothesis
ℵ₁ < 𝔠 lives in an arbitrary universe and is lowered to universe 0 with `lift_lt`.
The statements are copied verbatim, but without the `@[category …]` attribute (no
FormalConjecturesUtil import, as in the other results files).

Axioms (both theorems): propext, Classical.choice, Quot.sound

Date: 2026-11-14
