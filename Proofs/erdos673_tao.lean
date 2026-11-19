import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Real

namespace Erdos673

noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

lemma fin_dvd (n : ℕ) (hn : 0 < n) : (Set.ofPred (· ∣ n)).Finite := by
  apply n.divisors.finite_toSet.subset
  intro d hd
  simp only [Finset.mem_coe, Nat.mem_divisors]
  exact ⟨hd, hn.ne'⟩

lemma card_eq (n : ℕ) (hn : 0 < n) : (fin_dvd n hn).toFinset.card = n.divisors.card := by
  congr 1
  ext d
  simp only [Set.Finite.mem_toFinset, Nat.mem_divisors]
  exact ⟨fun h => ⟨h, hn.ne'⟩, fun h => h.1⟩

lemma G_eq (n : ℕ) : G n = ∑ j ∈ Finset.range (n.divisors.card - 1),
    (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
  Fin.sum_univ_eq_sum_range (fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1)) _

lemma G_le (n : ℕ) (hn : 0 < n) : G n ≤ n.divisors.card := by
  rw [G_eq]
  have hf := fin_dvd n hn
  have hc := card_eq n hn
  calc _ ≤ ∑ j ∈ Finset.range (n.divisors.card - 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        apply div_le_one_of_le₀
        · exact_mod_cast Nat.nth_le_nth_of_lt_card hf (Nat.le_succ j) (by omega)
        · positivity
    _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact_mod_cast Nat.sub_le _ _

lemma key (n m e : ℕ) (hn : 0 < n) (hm : 1 < m) (he : e ∣ n / m) (hmn : m ∣ n) :
    Nat.count (· ∣ n) e + 1 < n.divisors.card ∧
    (1 : ℝ) / m ≤ (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
      Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
  have hf := fin_dvd n hn
  have hc := card_eq n hn
  have hnm : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (by omega)
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hnm
  have hdiv : e ∣ n := he.trans (Nat.div_dvd_of_dvd hmn)
  have hem : e * m ∣ n := by
    obtain ⟨k, hk⟩ := he
    obtain ⟨l, hl⟩ := hmn
    refine ⟨k, ?_⟩
    have : n / m = l := by rw [hl, Nat.mul_div_cancel_left _ (by omega)]
    rw [hl, ← this, hk]; ring
  have hlt : e + 1 ≤ e * m := by nlinarith
  have h1 : Nat.count (· ∣ n) (e + 1) = Nat.count (· ∣ n) e + 1 :=
    Nat.count_succ_eq_succ_count_iff.2 hdiv
  have h2 : Nat.count (· ∣ n) (e + 1) ≤ Nat.count (· ∣ n) (e * m) := Nat.count_monotone _ hlt
  have h3 : Nat.count (· ∣ n) (e * m) < n.divisors.card := hc ▸ Nat.count_lt_card hf hem
  refine ⟨by omega, ?_⟩
  rw [Nat.nth_count (p := (· ∣ n)) hdiv]
  have h4 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) ≤ e * m := by
    calc _ ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) (e * m)) :=
          Nat.nth_le_nth_of_lt_card hf (by omega) (by omega)
      _ = e * m := Nat.nth_count (p := (· ∣ n)) hem
  have h5 : e < Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
    calc e = Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) := (Nat.nth_count (p := (· ∣ n)) hdiv).symm
      _ < _ := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) (by omega)
  have he' : (0 : ℝ) < e := by exact_mod_cast hepos
  have h4' : ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) ≤ (e : ℝ) * m := by
    exact_mod_cast h4
  have h5' : (0 : ℝ) < ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_le _).trans_lt h5
  calc (1 : ℝ) / m = e / (e * m) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left he'.le h5' h4'

theorem erdos_673.variants.tao (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card := by
  refine ⟨?_, G_le n hn⟩
  rw [G_eq]
  have hnm : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (by omega)
  have hinj : Set.InjOn (Nat.count (· ∣ n)) ((n / m).divisors : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∣ n := (Nat.dvd_of_mem_divisors ha).trans (Nat.div_dvd_of_dvd hmn)
    have hb' : b ∣ n := (Nat.dvd_of_mem_divisors hb).trans (Nat.div_dvd_of_dvd hmn)
    exact Nat.count_injective ha' hb' hab
  calc ((n / m).divisors.card : ℝ) / m = ∑ e ∈ (n / m).divisors, (1 : ℝ) / m := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ e ∈ (n / m).divisors, (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
          Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
        apply Finset.sum_le_sum
        intro e he
        exact (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).2
    _ = ∑ j ∈ (n / m).divisors.image (Nat.count (· ∣ n)),
          (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
        (Finset.sum_image (f := fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1))
          hinj).symm
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hj
          rw [Finset.mem_range]
          have := (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).1
          omega
        · intro j _ _
          positivity

end Erdos673

#print axioms Erdos673.erdos_673.variants.tao
