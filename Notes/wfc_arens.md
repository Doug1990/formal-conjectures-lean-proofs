# WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable

- Source: `FormalConjectures/Paper/WeaklyFirstCountable.lean:73` (category textbook)
- Date: 2026-10-31
- Compiles: 2 (1st: only a `haveI` style lint; 2nd clean)

Proof idea: an Arens-type space A = {∞} ∪ {aᵢ} ∪ {aᵢⱼ}. Its weak base is V(∞,n) = {∞} ∪ {aᵢ : i ≥ n},
V(aᵢ,n) = {aᵢ} ∪ {aᵢⱼ : j ≥ n}, and V(aᵢⱼ,n) = {aᵢⱼ}. The topology is *defined* as
{O | ∀ x ∈ O, ∃ k, V x k ⊆ O}. This is a topology because each V x is antitone, so weak first
countability holds by `Iff.rfl`. For ¬FirstCountable: take an antitone neighbourhood basis u_m
at ∞ and open sets O_m ⊆ u_m containing ∞, with thresholds n_m (for ∞) and k_m(i) (for aᵢ ∈ O_m).
Diagonalise with h(i) = max_{m ≤ i} k_m(i). The open set W = A ∖ {aᵢⱼ : j ≤ h(i)} contains ∞,
so u_m ⊆ W for some m. But with i = max(m, n_m), the point a_{i,h(i)} lies in O_m ⊆ u_m and not
in W. The class `WeaklyFirstCountableTopology` is restated locally, identical to the source (the
source imports FormalConjecturesUtil). The statement does not ask for any separation axiom, so none
is proved here.

Axioms: `[propext, Classical.choice, Quot.sound]`
