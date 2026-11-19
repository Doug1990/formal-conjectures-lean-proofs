# ame_4_2_not_exists

- Statement: `OpenQuantumProblem35.ame_4_2_not_exists : ¬ ExistsAME 4 2` (no 4-qubit AME state; Higuchi–Sudbery 2000)
- Source: `FormalConjectures/OpenQuantumProblems/35.lean:739` (category research solved)
- Verified file: `work/ame42.lean`. `results/ame_4_2_not_exists.lean` is a hand copy of it and was not compiled separately.
- Compiles: 2. Compile 1 passed with only two unused-`beta_reduce` lint warnings. Compile 2 was clean and included `#print axioms`.

## Proof idea
This is a singlet / shadow-inequality argument. For S ⊆ {0,1,2,3}, let P(S) = Σ_{x,y} ψ(x)ψ(y) ψ̄(mix_S x y) ψ̄(mix_S y x), which is Tr ρ_S². Per coordinate, I − SWAP = 2|singlet⟩⟨singlet|, which is a 16-case `decide` identity (`fb_sum`). Expanding the product over coordinates (`Fintype.prod_sum`) gives two expressions for one 4-fold sum M: M = Σ_S (−1)^{|S|} P(S) and M = T·conj(T), where T = Σ_x (−1)^{|x|} ψ(x) ψ(x̄). So M ≥ 0. For the AME side, each S of size ≤ 2 is a pattern `pat π U`: π moves S into the first two slots and U picks which of those slots lie in S. Reindexing along permuteConfig ∘ combineFirst (`reidx`) gives P(S) = Σ_{a,b} ρ(a, mixU a b) ρ(b, mixU b a). With ρ = I/4 this is cnt(U)/16, so P(∅) = 1, P({i}) = 1/2 and P({i,j}) = 1/4. Complements satisfy P(Sᶜ) = P(S). Covering all 16 subsets with 6 explicit permutations is a `decide +kernel` check (`cover_S`). The weighted sum is then 1 − 2 + 3/2 − 2 + 1 = −1/2 < 0, which contradicts M ≥ 0.

## Axioms
`'OpenQuantumProblem35.ame_4_2_not_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-05
