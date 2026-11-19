import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Find

namespace Mathoverflow75792

/-- The inductively defined predicate that `m` is reachable in `n` steps. -/
inductive Reachable : ℕ → ℕ → Prop
  | one : Reachable 1 1
  | add {m n a b} : Reachable m a → Reachable n b → Reachable (m + n) (a + b)
  | mul {m n a b} : Reachable m a → Reachable n b → Reachable (m * n) (a + b)

theorem Reachable.self (n : ℕ) (hn : 0 < n) : Reachable n n :=
  Nat.le_induction .one (fun _ _ ih ↦ .add ih .one) n hn

theorem not_reachable_zero_fst (n : ℕ) : ¬ Reachable 0 n := by
  intro h; generalize hm : 0 = m at h; induction h with
  | one => exact absurd hm (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hm; aesop
  | mul h₁ h₂ => rw [eq_comm, mul_eq_zero] at hm; aesop

theorem not_reachable_zero_snd (m : ℕ) : ¬ Reachable m 0 := by
  intro h; generalize hn : 0 = n at h; induction h with
  | one => exact absurd hn (by decide)
  | add h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop
  | mul h₁ h₂ => rw [eq_comm, add_eq_zero] at hn; aesop

theorem Reachable.dec {m n : ℕ} (h : Reachable m n) :
    ∃ m' n', m' + 1 = m ∧ n' + 1 = n := by
  obtain _ | m := m
  · exact absurd h (not_reachable_zero_fst _)
  obtain _ | n := n
  · exact absurd h (not_reachable_zero_snd _)
  exact ⟨_, _, rfl, rfl⟩

theorem Reachable.le {m n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (hm : Reachable m n₁) : Reachable m n₂ := by
  induction hn with
  | refl => exact hm
  | step h ih => convert ih.mul .one; simp

theorem reachable_iff_of_two_le (m n : ℕ) (hm : 2 ≤ m) :
    Reachable m n ↔ ∃ m₁, ∃ _ : m₁ < m, ∃ m₂, ∃ _ : m₂ < m, ∃ n₁, ∃ _ : n₁ < n, ∃ n₂, ∃ _ : n₂ < n,
      n₁ + n₂ = n ∧ Reachable m₁ n₁ ∧ Reachable m₂ n₂ ∧ (m₁ + m₂ = m ∨ m₁ * m₂ = m) := by
  refine ⟨fun hmn ↦ ?_, fun ⟨m₁, hm₁, m₂, hm₂, n₁, hn₁, n₂, hn₂, h₁, h₂, h₃, h₄⟩ ↦
    h₁ ▸ h₄.casesOn (· ▸ .add h₂ h₃) (· ▸ .mul h₂ h₃)⟩
  induction hmn with
  | one => exact absurd hm (by decide)
  | @add m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      refine ⟨m₃ + 1, ?_, m₄ + 1, ?_, n₃ + 1, ?_, n₄ + 1, ?_, rfl, h₁, h₂, .inl rfl⟩ <;> omega
  | @mul m₃ m₄ n₃ n₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨m₃, n₃, rfl, rfl⟩ := h₁.dec
      obtain ⟨m₄, n₄, rfl, rfl⟩ := h₂.dec
      obtain _ | m₃ := m₃
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₂ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅+n₃+1, ?_, n₆, ?_, by rw [← h₃]; ring, h₄.le ?_, h₅, ?_⟩
        all_goals omega
      obtain _ | m₄ := m₄
      · obtain ⟨m₅, hm₅, m₆, hm₆, n₅, hn₅, n₆, hn₆, h₃, h₄, h₅, h₆⟩ := ih₁ (by omega)
        refine ⟨m₅, ?_, m₆, ?_, n₅, ?_, n₆+n₄+1, ?_, by rw [← h₃]; ring, h₄, h₅.le ?_, ?_⟩
        all_goals omega
      refine ⟨m₃+2, ?_, m₄+2, ?_, _, ?_, _, ?_, rfl, h₁, h₂, .inr rfl⟩
      · refine (Nat.lt_mul_iff_one_lt_right ?_).2 ?_ <;> omega
      · refine (Nat.lt_mul_iff_one_lt_left ?_).2 ?_ <;> omega
      all_goals omega

def Reachable.decAux : ∀ (f m n : ℕ), m ≤ f → Decidable (Reachable m n)
  |     _,     0,     n,  _ => isFalse (not_reachable_zero_fst n)
  |     _,     1,     0,  _ => isFalse (not_reachable_zero_snd 1)
  |     _,     1, _ + 1,  _ => isTrue (Reachable.one.le (by lia))
  |     0, _ + 2,     _, hf => absurd hf (by lia)
  | f + 1, m + 2,     n, hf => by
      let d : ∀ {m₁} (h : m₁ < m + 2) {n}, Decidable (Reachable m₁ n) :=
        fun h ↦ Reachable.decAux f _ _ (by lia)
      refine @decidable_of_iff' _ _ (reachable_iff_of_two_le (m+2) n (by lia)) ?_
      refine Nat.decidableExistsLT' (I := fun m₁ hm₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun m₂ hm₂ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₁ hn₁ ↦ ?_)
      refine Nat.decidableExistsLT' (I := fun n₂ hn₂ ↦ ?_)
      refine instDecidableAnd (dq := ?_)
      refine instDecidableAnd (dp := d hm₁) (dq := ?_)
      exact instDecidableAnd (dp := d hm₂)
  termination_by structural f => f

instance Reachable.decide (m n : ℕ) : Decidable (Reachable m n) := Reachable.decAux m m n le_rfl

def complexity (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else Nat.find ⟨n, Reachable.self n <| n.pos_of_ne_zero h⟩

theorem Reachable.complexity_le {m n : ℕ} (h : Reachable m n) : complexity m ≤ n := by
  unfold complexity
  split_ifs with h'
  · subst h'; exact absurd h (not_reachable_zero_fst n)
  exact Nat.find_min' _ h

theorem Reachable.complexity {n : ℕ} (hn : 0 < n) : Reachable n (complexity n) := by
  unfold Mathoverflow75792.complexity
  rw [dif_neg (ne_of_gt hn)]
  exact Nat.find_spec _

theorem Reachable.pow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Reachable (m ^ n) (m * n) := by
  induction hn with
  | refl => convert Reachable.self m hm <;> simp
  | step hn ih => exact .mul ih (.self m hm)

/-! ## New material -/

/-- `(1 + n)^3 ≤ 3^(a+b)` given the bounds for `1` (cost `a ≥ 1`) and `n` (cost `b`). -/
lemma add_one_case (n a b : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) (hnb : n ^ 3 ≤ 3 ^ b) :
    (1 + n) ^ 3 ≤ 3 ^ (a + b) := by
  have h3a : 3 ≤ 3 ^ a := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hab : 3 ^ (a + b) = 3 ^ a * 3 ^ b := pow_add 3 a b
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
    · -- 8 ≤ 3^(a+b), a+b ≥ 2
      calc (1 + 1) ^ 3 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · -- b ≥ 2 since 8 ≤ 3^b
      have hb2 : 2 ≤ b := by
        by_contra hc
        have : b = 1 := by omega
        subst this; norm_num at hnb
      calc (1 + 2) ^ 3 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have key : (1 + (k + 3)) ^ 3 ≤ 3 * (k + 3) ^ 3 := by
      nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2), Nat.zero_le k]
    calc (1 + (k + 3)) ^ 3 ≤ 3 * (k + 3) ^ 3 := key
      _ ≤ 3 ^ a * 3 ^ b := Nat.mul_le_mul h3a hnb
      _ = 3 ^ (a + b) := hab.symm

lemma cube_le (m k : ℕ) (h : Reachable m k) : 1 ≤ m ∧ 1 ≤ k ∧ m ^ 3 ≤ 3 ^ k := by
  induction h with
  | one => norm_num
  | @add m n a b _ _ ih₁ ih₂ =>
      obtain ⟨hm, ha, hma⟩ := ih₁
      obtain ⟨hn, hb, hnb⟩ := ih₂
      refine ⟨by omega, by omega, ?_⟩
      rcases Nat.lt_or_ge m 2 with h1 | h1
      · have : m = 1 := by omega
        subst this
        exact add_one_case n a b hn ha hb hnb
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have : n = 1 := by omega
        subst this
        rw [add_comm m 1, add_comm a b]
        exact add_one_case m b a hm hb ha hma
      have hle : m + n ≤ m * n := by nlinarith
      calc (m + n) ^ 3 ≤ (m * n) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = m ^ 3 * n ^ 3 := by ring
        _ ≤ 3 ^ a * 3 ^ b := Nat.mul_le_mul hma hnb
        _ = 3 ^ (a + b) := (pow_add 3 a b).symm
  | @mul m n a b _ _ ih₁ ih₂ =>
      obtain ⟨hm, ha, hma⟩ := ih₁
      obtain ⟨hn, hb, hnb⟩ := ih₂
      refine ⟨Nat.mul_le_mul hm hn, by omega, ?_⟩
      calc (m * n) ^ 3 = m ^ 3 * n ^ 3 := by ring
        _ ≤ 3 ^ a * 3 ^ b := Nat.mul_le_mul hma hnb
        _ = 3 ^ (a + b) := (pow_add 3 a b).symm

theorem complexity_three_pow : ∀ n : ℕ, 0 < n → complexity (3 ^ n) = 3 * n := by
  intro n hn
  apply le_antisymm
  · exact (Reachable.pow 3 n (by norm_num) hn).complexity_le
  · have h := (cube_le _ _ (Reachable.complexity (n := 3 ^ n) (pow_pos (by norm_num) n))).2.2
    rw [← pow_mul, mul_comm n 3] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

end Mathoverflow75792

#print axioms Mathoverflow75792.complexity_three_pow
