import Mathlib.Combinatorics.Configuration
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.IsPrimePow

open Configuration

namespace Erdos723

namespace PP

/-- If `o² + o + 1 = q² + q + 1` then `o = q`. -/
lemma sq_inj {o q : ℕ} (h : o ^ 2 + o + 1 = q ^ 2 + q + 1) : o = q := by
  rcases lt_trichotomy o q with hlt | heq | hgt
  · have : o ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    omega
  · exact heq
  · have : q ^ 2 < o ^ 2 := Nat.pow_lt_pow_left hgt (by norm_num)
    omega

open scoped LinearAlgebra.Projectivization in
/-- The projective plane over a finite field `K` has order `|K|`. -/
lemma order_ofField (K : Type) [Field K] [Finite K] [DecidableEq K] :
    @ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) _ _ = Nat.card K := by
  have : Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _
  have h1 := ProjectivePlane.card_points (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  have h2 := Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp)
  rw [Fintype.card_eq_nat_card, h2] at h1
  simp [Finset.sum_range_succ] at h1
  apply sq_inj
  linarith

end PP

open scoped LinearAlgebra.Projectivization in
/--
These always exist if $n$ is a prime power.
-/
theorem erdos_723.variants.prime_power_is_projplane_order :
    ∀ n, IsPrimePow n → ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = n := by
  classical
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p k
  refine ⟨ℙ K (Fin 3 → K), ℙ K (Fin 3 → K), inferInstance, Fintype.ofFinite _, Fintype.ofFinite _, inferInstance, ?_⟩
  rw [PP.order_ofField (GaloisField p k), GaloisField.card p k hk.ne']

end Erdos723

#print axioms Erdos723.erdos_723.variants.prime_power_is_projplane_order
