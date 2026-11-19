# fernandes4

- Statements: `Arxiv.«2605.12342».conjecture_1.variants.rank_4_3` and `conjecture_1.variants.rank_4_4` (Γ_{4⊕3} and Γ_{4⊕4} are not 2-generated)
- Source: `FormalConjectures/Arxiv/2605.12342/Conjecture1.lean:136` and `:144` (category research solved)
- Verified file: `work/fernandes4.lean` (copied here as `fernandes4.lean`; it also contains the rank_3_3 proof from `fernandes33.lean`)

Proof idea: S₄ acts on the three ways to split {0,1,2,3} into two pairs. This gives a homomorphism φ : S₄ → S₃ (`phi`), defined explicitly by `gS σ k = pr (σ 0) (σ (k+1))`. Multiplicativity is checked by `decide +kernel` only for products swap·ρ, and then extended to all σ by swap induction. φ is surjective (`decide`) and preserves the sign (checked on swaps, then swap induction). So (σ₁, σ₂) ↦ (φσ₁, σ₂) and (σ₁, σ₂) ↦ (φσ₁, φσ₂) are surjective homomorphisms Γ_{4⊕3} → Γ_{3⊕3} and Γ_{4⊕4} → Γ_{3⊕3}. If Γ_{4⊕n} = ⟨a, b⟩, then Γ_{3⊕3} = ⟨f a, f b⟩ (`not2_of_surj`, using `MonoidHom.map_closure`). That contradicts rank_3_3, which is proved in the same file (see fernandes33.md).

Axioms (both theorems): `[propext, Classical.choice, Quot.sound]`

Date: 2026-11-01
