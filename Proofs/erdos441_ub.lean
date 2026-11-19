import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace Erdos441

noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}

namespace UB

lemma key {a b N : ℕ} (ha : 0 < a) (hab : a < b) (hl : Nat.lcm a b ≤ N) : N / b < N / a := by
  have hg : Nat.gcd a b ≤ b - a :=
    Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))
  have h1 : a * b ≤ (b - a) * N := by
    rw [← Nat.gcd_mul_lcm a b]; exact Nat.mul_le_mul hg hl
  have hq : N / b * b ≤ N := Nat.div_mul_le_self N b
  have h3 : a * (N / b * b) ≤ a * N := Nat.mul_le_mul_left a hq
  have h2 : (N / b + 1) * a ≤ N := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < b by omega)
    calc b * ((N / b + 1) * a) = a * (N / b * b) + a * b := by ring
      _ ≤ a * N + (b - a) * N := Nat.add_le_add h3 h1
      _ = b * N := by rw [← Nat.add_mul, Nat.add_sub_of_le hab.le]
  exact (Nat.le_div_iff_mul_le ha).mpr h2

lemma card_le (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hl : ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) : A.card ≤ 2 * Nat.sqrt N + 1 := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => by
    have := hA ha
    rw [Finset.mem_Icc] at this
    omega
  rw [← Finset.card_filter_add_card_filter_not (s := A) (p := fun a => a ≤ Nat.sqrt N)]
  have c1 : (A.filter (fun a => a ≤ Nat.sqrt N)).card ≤ Nat.sqrt N := by
    have hsub : A.filter (fun a => a ≤ Nat.sqrt N) ⊆ Finset.Icc 1 (Nat.sqrt N) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have := hpos a ha.1
      rw [Finset.mem_Icc]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have c2 : (A.filter (fun a => ¬ a ≤ Nat.sqrt N)).card ≤ Nat.sqrt N + 1 := by
    have := Finset.card_le_card_of_injOn (fun a => N / a)
      (s := A.filter (fun a => ¬ a ≤ Nat.sqrt N)) (t := Finset.range (Nat.sqrt N + 1))
      (by
        intro a ha
        rw [Finset.mem_coe, Finset.mem_filter] at ha
        rw [Finset.mem_coe, Finset.mem_range]
        have ha0 := hpos a ha.1
        rw [Nat.div_lt_iff_lt_mul ha0]
        have h1 := Nat.lt_succ_sqrt' N
        have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ (Nat.sqrt N + 1) * a :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.succ_eq_add_one, pow_two] at h1
        omega)
      (by
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_filter] at ha hb
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := key (hpos a ha.1) h (hl a ha.1 b hb.1)
          simp only at hab
          omega
        · have := key (hpos b hb.1) h (hl b hb.1 a ha.1)
          simp only at hab
          omega)
    rw [Finset.card_range] at this
    exact this
  omega

end UB

theorem erdos_441.variants.erdos_upper_bound :
    ∃ C : ℝ, ∀ N : ℕ, (g N : ℝ) ≤ √(4 * N) + C := by
  refine ⟨1, fun N => ?_⟩
  have hg : g N ≤ 2 * Nat.sqrt N + 1 := by
    apply csSup_le'
    rintro k ⟨A, hA, hl, rfl⟩
    exact UB.card_le N A hA hl
  have h4 : √(4 * (N : ℝ)) = 2 * √(N : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
      Real.sqrt_mul_self (by norm_num)]
  rw [h4]
  have h5 := Real.nat_sqrt_le_real_sqrt (a := N)
  have hc : (g N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) + 1 := by exact_mod_cast hg
  linarith

end Erdos441

#print axioms Erdos441.erdos_441.variants.erdos_upper_bound
