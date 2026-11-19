import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum.Prime

namespace OeisA51903

/-- Maximum exponent in the prime factorization of $n$. -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

namespace P

/-- modular exponentiation by squaring, with fuel -/
def pm (m b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | k + 1, e => pm m b k (e / 2) ^ 2 * b ^ (e % 2) % m

theorem pm_eq (m b : ℕ) : ∀ k e, e < 2 ^ k → pm m b k e = b ^ e % m := by
  intro k
  induction k with
  | zero =>
    intro e he
    have : e = 0 := by simpa using he
    subst this
    simp [pm]
  | succ k ih =>
    intro e he
    have h2 : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    simp only [pm]
    rw [ih _ h2]
    have : b ^ e = (b ^ (e / 2)) ^ 2 * b ^ (e % 2) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [this]
    exact ((Nat.mod_modEq _ _).pow 2).mul_right _

theorem factors :
    Nat.primeFactorsList 9687963167864344937 = [7, 631, 881, 3511, 3511, 201961] := by
  have h7 : Nat.Prime 7 := by norm_num
  have h631 : Nat.Prime 631 := by norm_num
  have h881 : Nat.Prime 881 := by norm_num
  have h3511 : Nat.Prime 3511 := by norm_num
  have h201961 : Nat.Prime 201961 := by norm_num
  have hperm := Nat.primeFactorsList_unique (n := 9687963167864344937)
    (l := [7, 631, 881, 3511, 3511, 201961]) (by norm_num) (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
  exact (List.Perm.eq_of_sortedLE (List.Pairwise.sortedLE (by decide))
    (Nat.primeFactorsList_sorted _) hperm).symm

theorem a_eq : a 9687963167864344937 = 2 := by
  unfold a
  rw [factors]
  decide

theorem modeq : 2 ^ 9687963167864344937 ≡ 2 ^ 2 [MOD 9687963167864344937] := by
  unfold Nat.ModEq
  rw [← pm_eq 9687963167864344937 2 64 9687963167864344937 (by decide +kernel)]
  decide +kernel

end P

theorem conjecture3 :
    ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  refine ⟨9687963167864344937, ⟨4843981583932172468, by norm_num⟩, ?_, ?_⟩
  · rw [P.a_eq]; decide
  · rw [P.a_eq]; exact P.modeq

end OeisA51903

#print axioms OeisA51903.conjecture3
