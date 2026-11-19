import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases

namespace Erdos682

/-- The `n`th prime, indexed from zero: `p 0 = 2`, `p 1 = 3`, ... -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Every number strictly between `2183 + 30030 d` and `2201 + 30030 d` has a prime factor
`≤ 13` (it already holds for `2184, …, 2200`, and `30030 = 2·3·5·7·11·13`). -/
lemma key (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 17) :
    ∃ r, 2 ≤ r ∧ r ≤ 13 ∧ r ∣ 2183 + 30030 * d + k := by
  interval_cases k <;>
    first
    | exact ⟨2, by omega, by omega, by omega⟩
    | exact ⟨3, by omega, by omega, by omega⟩
    | exact ⟨5, by omega, by omega, by omega⟩
    | exact ⟨7, by omega, by omega, by omega⟩
    | exact ⟨11, by omega, by omega, by omega⟩
    | exact ⟨13, by omega, by omega, by omega⟩

lemma not_prime (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 17) :
    ¬ (2183 + 30030 * d + k).Prime := by
  intro hp
  obtain ⟨r, hr2, hr13, hr⟩ := key d k hk1 hk2
  rcases hp.eq_one_or_self_of_dvd r hr with h | h <;> omega

lemma filter_eq (d : ℕ) (h₁ : (2183 + 30030 * d).Prime) :
    (Finset.range 18).filter (fun k => Nat.Prime (2183 + 30030 * d + k)) = {0} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hp⟩
    by_contra hk0
    exact not_prime d k (by omega) (by omega) hp
  · rintro rfl
    exact ⟨by omega, by simpa using h₁⟩

theorem erdos_682.variants.dickson_counterexample (d : ℕ) (h₁ : (2183 + 30030 * d).Prime)
    (h₂ : (2201 + 30030 * d).Prime) : ∃ n, p n = 2183 + 30030 * d ∧ p (n + 1) = 2201 + 30030 * d ∧
      ∀ m ∈ Set.Ioo (p n) (p (n + 1)), m.minFac < p (n + 1) - p n := by
  have hc : Nat.count Nat.Prime (2201 + 30030 * d) =
      Nat.count Nat.Prime (2183 + 30030 * d) + 1 := by
    have e : 2201 + 30030 * d = (2183 + 30030 * d) + 18 := by omega
    rw [e, Nat.count_add, Nat.count_eq_card_filter_range (fun k => Nat.Prime (2183 + 30030 * d + k)),
      filter_eq d h₁, Finset.card_singleton]
  have hp1 : p (Nat.count Nat.Prime (2183 + 30030 * d)) = 2183 + 30030 * d := Nat.nth_count h₁
  have hp2 : p (Nat.count Nat.Prime (2183 + 30030 * d) + 1) = 2201 + 30030 * d := by
    rw [← hc]; exact Nat.nth_count h₂
  refine ⟨Nat.count Nat.Prime (2183 + 30030 * d), hp1, hp2, ?_⟩
  rw [hp1, hp2]
  rintro m ⟨hm1, hm2⟩
  obtain ⟨r, hr2, hr13, hr⟩ := key d (m - (2183 + 30030 * d)) (by omega) (by omega)
  have e : 2183 + 30030 * d + (m - (2183 + 30030 * d)) = m := by omega
  rw [e] at hr
  have := Nat.minFac_le_of_dvd hr2 hr
  omega

end Erdos682

#print axioms Erdos682.erdos_682.variants.dickson_counterexample
