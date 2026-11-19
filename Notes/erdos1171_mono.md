# Erdos1171.erdos_1171.variants.mono_k

- Source: FormalConjectures/ErdosProblems/1171.lean:62 (category API)
- Statement: OrdinalMultiColorRamsey (ω₁²) (ω₁·ω) 3 k → OrdinalMultiColorRamsey (ω₁²) (ω₁·ω) 3 j for j ≤ k.
- `OrdinalMultiColorRamsey` is restated locally from
  FormalConjecturesForMathlib/SetTheory/Ordinal/PartitionRelation.lean (verbatim).

Proof idea: given a (j+1)-colouring, compose it with `Fin.castLE` to get a (k+1)-colouring. A
colour-0 set of type ω₁·ω pulls back unchanged. A set of size 3 monochromatic in colour i+1
has two distinct points, so i+1 is a value of the original colouring and i < j. (The size-3
condition rules out the degenerate case of a set with fewer than two points; the generic lemma
`mono_gen` assumes 1 < γ.) Subtlety: as written in the source, the hypothesis and the
conclusion have independent auto-bound universe parameters (ω_ 1 etc. are
universe-polymorphic). So the proof first transfers the hypothesis across universes
(`transfer`), using an order isomorphism α.ToType ≃o α'.ToType from `Ordinal.lift_type_eq`.
Images keep order type (`RelIso.ordinal_lift_type_eq`) and cardinality (`Cardinal.lift_mk_eq'`),
and `Ordinal.lift_omega` / `lift_mul` / `lift_ofNat` identify the lifted parameters.

Axioms: `'Erdos1171.erdos_1171.variants.mono_k' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-11-09
