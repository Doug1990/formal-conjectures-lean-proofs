import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos1148

/--
The weaker property: $n = x^2 + y^2 - z^2$ such that $\max(x^2, y^2, z^2) \leq n + 2\sqrt{n}$.
-/
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

lemma sq_lift {p q : ℕ} (h : p ≤ q) : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h 2

/-- Natural-number version with `Nat.sqrt`. -/
lemma key (n : ℕ) : ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    x ^ 2 ≤ n + 2 * Nat.sqrt n ∧ y ^ 2 ≤ n + 2 * Nat.sqrt n ∧
    z ^ 2 ≤ n + 2 * Nat.sqrt n := by
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  generalize Nat.sqrt n = a at h1 h2 ⊢
  have e : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
  have e' : a.succ ^ 2 = a ^ 2 + 2 * a + 1 := by rw [Nat.succ_eq_add_one]; ring
  obtain ⟨r, hr⟩ : ∃ r, n = a ^ 2 + r := ⟨n - a ^ 2, by omega⟩
  subst hr
  have hra : r ≤ 2 * a := by omega
  rcases Nat.even_or_odd' r with ⟨t, rfl | rfl⟩
  · rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
    · rcases s with _ | w
      · exact ⟨a, 0, 0, by simp, by omega, by simp, by simp⟩
      · refine ⟨a, w + 2, w, ?_, by omega, ?_, ?_⟩
        · have : (w + 2) ^ 2 = w ^ 2 + 4 * w + 4 := by ring
          omega
        · have := sq_lift (show w + 2 ≤ a by omega); omega
        · have := sq_lift (show w ≤ a by omega); omega
    · obtain ⟨u, hu⟩ : ∃ u, a = u + 2 * s + 1 := ⟨a - 2 * s - 1, by omega⟩
      refine ⟨a + 1, u, u + 1, ?_, by omega, ?_, ?_⟩
      · have : (u + 1) ^ 2 = u ^ 2 + 2 * u + 1 := by ring
        omega
      · have := sq_lift (show u ≤ a by omega); omega
      · have := sq_lift (show u + 1 ≤ a by omega); omega
  · refine ⟨a, t + 1, t, ?_, by omega, ?_, ?_⟩
    · have : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      omega
    · have := sq_lift (show t + 1 ≤ a by omega); omega
    · have := sq_lift (show t ≤ a by omega); omega

lemma cast_bound (n m : ℕ) (h : m ^ 2 ≤ n + 2 * Nat.sqrt n) :
    (m ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n := by
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have h' : ((m ^ 2 : ℕ) : ℝ) ≤ ((n + 2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/--
[Va99] reports this is 'obvious' if we replace $\leq n$ with $\leq n+2\sqrt{n}$.
-/
theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n := by
  intro n
  obtain ⟨x, y, z, h, hx, hy, hz⟩ := key n
  exact ⟨x, y, z, h, cast_bound n x hx, cast_bound n y hy, cast_bound n z hz⟩

end Erdos1148

#print axioms Erdos1148.erdos_1148.variants.weaker
