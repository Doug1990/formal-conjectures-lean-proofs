# petersen_normal5

- Statement: `PetersenColoringConjecture.petersen_coloring_conjecture.variants.normal_five_edge_coloring` (research solved, Jaeger 1988)
- Source: `FormalConjectures/Wikipedia/PetersenColoringConjecture.lean:79` (Petersen graph defs restated from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Petersen.lean`)

## Proof idea
The Petersen graph P = K(5,2) carries the edge colouring col({a,b}) = the unique element of Fin 5 outside a ∪ b. The colours at a vertex w are exactly the complement of w, and they are distinct; these P facts are checked by `decide +kernel` over the 10 vertices. (⇒) c = col ∘ φ. Edges at v go injectively to the edges at w_v, so c is proper. For an edge uv, the 5 edges around it map onto the edges at w_u and w_v. φ(uv) lies at both, so w_u = w_v (3 colours) or w_u ~ w_v (disjoint complements, 5 colours). (⇐) Let S_v be the 3-set of colours at v and w_v = complement of S_v. Normality gives S_u = S_v or S_u ∩ S_v = {c(uv)}, since |S_u ∪ S_v| + |S_u ∩ S_v| = 6. Set φ(uv) = {w_u, nb(w_u, c(uv))}, where nb(w,i) = complement of w ∪ {i}. In both cases this is symmetric in u and v (for a rich edge nb(w_u, i) = w_v). φ is injective at v because col recovers c, and its image is all of the incidence set at w_v by a card argument (3 = 3).

## Axioms
`[propext, Classical.choice, Quot.sound]`

Date: 2026-11-03. 2 compiles (1: a beta-redex in the `Sym2.lift` symmetry proof plus deprecations `card_univ_diff` → `card_univ_sdiff`; 2: clean + axioms). The results copy was written from the verified work file `work/petersen_normal5.lean`.
