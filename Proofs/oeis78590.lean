import Mathlib.Tactic.NormNum

namespace OeisA78590

/-- $a(1)=1, a(2)=1, a(n)=(2^{a(n-1)} + 1)/a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => (2 ^ a (n + 2) + 1) / a (n + 1)

lemma a5 : a 5 = 171 := by rfl

lemma a6 : a 6 % 18 = 3 := by rfl

lemma key (b : ℕ) (hb : b % 18 = 3) : ¬ 171 ∣ 2 ^ b + 1 := by
  intro h7
  have h19 : 19 ∣ 2 ^ b + 1 := Nat.dvd_trans ⟨9, rfl⟩ h7
  obtain ⟨q, hq⟩ : ∃ q, b = 18 * q + 3 := ⟨b / 18, by omega⟩
  rw [hq, pow_add, pow_mul] at h19
  have h1 : (2 ^ 18) ^ q % 19 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : ((2 ^ 18) ^ q * 2 ^ 3 + 1) % 19 = 9 := by
    rw [Nat.add_mod, Nat.mul_mod, h1]
    norm_num
  omega

theorem conjecture :
    ¬ ∀ n : ℕ, 3 ≤ n → a (n - 2) ∣ 2 ^ a (n - 1) + 1 := by
  intro h
  have h7 := h 7 (by omega)
  generalize hb : a (7 - 1) = b at h7
  have hb' : b % 18 = 3 := by rw [← hb]; exact a6
  have h5 : a (7 - 2) = 171 := a5
  rw [h5] at h7
  exact key b hb' h7

end OeisA78590

#print axioms OeisA78590.conjecture
