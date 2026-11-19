import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos674

/-- Restated from FormalConjectures/ErdosProblems/674.lean. -/
def solutionSet : Set (ℕ × ℕ × ℕ) :=
  {(x, y, z) | 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z}

namespace KO

/-- Ko's family: with `N = 2^n = a + 1`, `a = n + k`, `W = 2^(2Nk) a^(2a)`,
the triple `(N²W, a²W, 2NaW)` solves `x^x y^y = z^z`. -/
lemma key (n k a N W : ℕ) (ha : a = n + k) (hN : N = n + k + 1) (h2 : 2 ^ n = N)
    (hW : W = 2 ^ (2 * N * k) * a ^ (2 * a)) :
    (N ^ 2 * W) ^ (N ^ 2 * W) * (a ^ 2 * W) ^ (a ^ 2 * W) =
      (2 * N * a * W) ^ (2 * N * a * W) := by
  have pw : ∀ p q m : ℕ, (2 ^ p * a ^ q) ^ m = 2 ^ (p * m) * a ^ (q * m) := by
    intro p q m; rw [mul_pow, ← pow_mul, ← pow_mul]
  have hx : N ^ 2 * W = 2 ^ (2 * N * k + 2 * n) * a ^ (2 * a) := by
    rw [hW, show N ^ 2 = 2 ^ (2 * n) by rw [← h2, ← pow_mul, mul_comm], pow_add]; ring
  have hy : a ^ 2 * W = 2 ^ (2 * N * k) * a ^ (2 * a + 2) := by
    rw [hW, pow_add]; ring
  have hz : 2 * N * a * W = 2 ^ (2 * N * k + n + 1) * a ^ (2 * a + 1) := by
    rw [hW, show 2 * N = 2 ^ (n + 1) by rw [← h2, pow_succ]; ring, pow_add, pow_add, pow_add]
    ring
  have e1 : ∀ m, (N ^ 2 * W) ^ m = 2 ^ ((2 * N * k + 2 * n) * m) * a ^ (2 * a * m) := by
    intro m; rw [hx, pw]
  have e2 : ∀ m, (a ^ 2 * W) ^ m = 2 ^ ((2 * N * k) * m) * a ^ ((2 * a + 2) * m) := by
    intro m; rw [hy, pw]
  have e3 : ∀ m, (2 * N * a * W) ^ m = 2 ^ ((2 * N * k + n + 1) * m) * a ^ ((2 * a + 1) * m) := by
    intro m; rw [hz, pw]
  have E1 : (2 * N * k + 2 * n) * (N ^ 2 * W) + (2 * N * k) * (a ^ 2 * W) =
      (2 * N * k + n + 1) * (2 * N * a * W) := by
    subst ha hN; ring
  have E2 : 2 * a * (N ^ 2 * W) + (2 * a + 2) * (a ^ 2 * W) = (2 * a + 1) * (2 * N * a * W) := by
    subst ha hN; ring
  rw [e1, e2, e3, ← E1, ← E2, pow_add, pow_add]
  ring

/-- The member of Ko's family for `n ≥ 2`. -/
lemma mem (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y z : ℕ, (x, y, z) ∈ solutionSet ∧ 2 ^ n ≤ x := by
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hlt2 : n + 1 < 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 2 ^ (2 + m) = 4 * 2 ^ m := by rw [pow_add]; norm_num
    have : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  set k := 2 ^ n - 1 - n with hk
  set N := n + k + 1 with hNdef
  set a := n + k with hadef
  set W := 2 ^ (2 * N * k) * a ^ (2 * a) with hWdef
  have h2 : 2 ^ n = N := by omega
  have hW : 1 ≤ W := by
    have : 0 < a := by omega
    have : 0 < W := by rw [hWdef]; positivity
    omega
  have hN2 : 2 ≤ N := by omega
  have ha2 : 2 ≤ a := by omega
  refine ⟨N ^ 2 * W, a ^ 2 * W, 2 * N * a * W, ⟨?_, ?_, ?_, key n k a N W rfl rfl h2 rfl⟩, ?_⟩
  · nlinarith
  · nlinarith
  · have : 4 ≤ N * a := Nat.mul_le_mul hN2 ha2
    have : 4 ≤ N * a * W := le_trans this (Nat.le_mul_of_pos_right _ hW)
    nlinarith
  · rw [h2]
    have : N ≤ N ^ 2 := by nlinarith
    exact le_trans this (Nat.le_mul_of_pos_right _ hW)

end KO

theorem erdos_674 : solutionSet.Nonempty := by
  obtain ⟨x, y, z, h, -⟩ := KO.mem 2 le_rfl
  exact ⟨_, h⟩

theorem erdos_674.variants.infinite : solutionSet.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨x, y, z, h, hx⟩ := KO.mem (B + 2) (by omega)
  have h1 : x ≤ B := hB ⟨(x, y, z), h, rfl⟩
  have h3 : B + 2 < 2 ^ (B + 2) := Nat.lt_two_pow_self
  omega

end Erdos674

#print axioms Erdos674.erdos_674
#print axioms Erdos674.erdos_674.variants.infinite
