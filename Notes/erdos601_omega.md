# Erdos601.erdos_601.variants.at_omega

- Source: `FormalConjectures/ErdosProblems/601.lean`, line 122 (category research solved)
- Date: 2026-11-10

**Proof idea.** First a Ramsey-type lemma on ℕ (`R.ramsey_nat`): starting from S₀ = ℕ, repeatedly take x = min S and pass to S' = (S ∩ N(x)) \ {x} if that set is infinite, otherwise to (S \ N(x)) \ {x}. This gives a strictly increasing sequence x₀ < x₁ < … where each xᵢ is adjacent to all later x's (colour c i) or to none of them. If c holds infinitely often, `Nat.nth` enumerates those indices and gives an injective infinite path (in fact a clique). Otherwise c fails from some N on, and {x_{N+1+k}} is an infinite independent set. Then transfer to ω.ToType: an order isomorphism ℕ ≃o ω.ToType comes from `Ordinal.lift_type_eq` (`type_nat_lt`, `type_toType`). Pull the graph back along it, and note that an infinite subset of ℕ has order type ω (`Nat.Subtype.orderIsoOfNat`). Order types are preserved under the image (`typeLT_image`, reused from erdos1171_mono).

Axioms: `propext, Classical.choice, Quot.sound`
