import Mathlib

namespace OeisA100474

def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod (Nat.nth Nat.Prime) -
      a (n + 1)

lemma count_23 : Nat.count Nat.Prime 23 = 8 := by
  simp only [Nat.count_succ, Nat.count_zero]
  norm_num

lemma count_19 : Nat.count Nat.Prime 19 = 7 := by
  simp only [Nat.count_succ, Nat.count_zero]
  norm_num

lemma count_17 : Nat.count Nat.Prime 17 = 6 := by
  simp only [Nat.count_succ, Nat.count_zero]
  norm_num

lemma count_13 : Nat.count Nat.Prime 13 = 5 := by
  simp only [Nat.count_succ, Nat.count_zero]
  norm_num

lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  rw [← count_13]; exact Nat.nth_count (by norm_num)

lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  rw [← count_17]; exact Nat.nth_count (by norm_num)

lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  rw [← count_19]; exact Nat.nth_count (by norm_num)

lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  rw [← count_23]; exact Nat.nth_count (by norm_num)

theorem a_1 : a 1 = 1 := by rfl

theorem a_2 : a 2 = 5 := by
  change (Finset.Ico 0 2).prod (Nat.nth Nat.Prime) - a 1 = 5
  rw [a_1, Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  norm_num

theorem a_3 : a 3 = 380 := by
  change (Finset.Ico 2 5).prod (Nat.nth Nat.Prime) - a 2 = 380
  rw [a_2, Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num),
    Finset.prod_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  norm_num

theorem a_4 : a 4 = 96197 := by
  change (Finset.Ico 5 9).prod (Nat.nth Nat.Prime) - a 3 = 96197
  rw [a_3, Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num),
    Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_five, nth_prime_six, nth_prime_seven, nth_prime_eight]
  norm_num

lemma nth_prime_of_count {p k : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]; exact Nat.nth_count hp

theorem a_5 : a 5 = 58546472 := by
  change (Finset.Ico 9 14).prod (Nat.nth Nat.Prime) - a 4 = 58546472
  rw [a_4, Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num),
    Finset.prod_Ico_succ_top (by norm_num), Finset.prod_Ico_succ_top (by norm_num),
    Finset.prod_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_of_count (p := 29) (by norm_num)
      (by simp only [Nat.count_succ, Nat.count_zero]; norm_num),
    nth_prime_of_count (p := 31) (by norm_num)
      (by simp only [Nat.count_succ, Nat.count_zero]; norm_num),
    nth_prime_of_count (p := 37) (by norm_num)
      (by simp only [Nat.count_succ, Nat.count_zero]; norm_num),
    nth_prime_of_count (p := 41) (by norm_num)
      (by simp only [Nat.count_succ, Nat.count_zero]; norm_num),
    nth_prime_of_count (p := 43) (by norm_num)
      (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)]
  norm_num

end OeisA100474

#print axioms OeisA100474.a_5

#print axioms OeisA100474.a_2
#print axioms OeisA100474.a_3
#print axioms OeisA100474.a_4
