# green35_young

- Statement: `Green35.variants.c_inf_lower_young : (c 2) ^ 2 ≤ c ∞` (category textbook)
- Source: `FormalConjectures/GreensOpenProblems/35.lean:119` in the checkout. The definitions `IsUnitIntervalDensity` and `c` are restated verbatim (namespace `Green35`; the `variants` sub-namespace and the `@[category]` attribute are dropped because FormalConjecturesUtil is not built).
- Proof idea: for a unit-interval density f, g = f ⋆ f is nonnegative and integrable with ∫ g = (∫ f)² = 1 (`integral_convolution`), so ∫⁻ ‖g‖ₑ = 1. Pointwise a.e. ‖g x‖ₑ ≤ ‖g‖_∞, so ‖g‖₂² = ∫⁻ ‖g‖ₑ² ≤ ‖g‖_∞ · ∫⁻ ‖g‖ₑ = ‖g‖_∞. With c(2) ≤ ‖g‖₂ this gives c(2)² ≤ ‖g‖_∞ for every f, and `le_sInf` gives c(2)² ≤ c(∞).
- Axioms: `'Green35.c_inf_lower_young' depends on axioms: [propext, Classical.choice, Quot.sound]`
- Date: 2026-11-01
