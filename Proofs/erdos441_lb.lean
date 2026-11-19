import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace Erdos441

noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}

namespace LB

/-- the set used: [1, s] ∪ {2j : s/2 < j ≤ s} -/
def A (s : ℕ) : Finset ℕ :=
  Finset.Icc 1 s ∪ (Finset.Ioc (s / 2) s).image (fun j => 2 * j)

lemma lcm_le_mul (a b : ℕ) : Nat.lcm a b ≤ a * b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  exact Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd_mul a b)

lemma card_A (s : ℕ) : (A s).card = s + (s - s / 2) := by
  unfold A
  rw [Finset.card_union_of_disjoint, Nat.card_Icc,
    Finset.card_image_of_injective _ (fun a b (h : 2 * a = 2 * b) => by omega), Nat.card_Ioc]
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_image] at hx'
    obtain ⟨j, hj, rfl⟩ := hx'
    rw [Finset.mem_Ioc] at hj
    omega

lemma mem_A {s x : ℕ} (hx : x ∈ A s) :
    (1 ≤ x ∧ x ≤ s) ∨ (∃ j, 1 ≤ j ∧ j ≤ s ∧ x = 2 * j) := by
  unfold A at hx
  rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_image] at hx
  rcases hx with h | ⟨j, hj, rfl⟩
  · exact Or.inl h
  · rw [Finset.mem_Ioc] at hj
    exact Or.inr ⟨j, by omega, hj.2, rfl⟩

lemma good (N s : ℕ) (hs : 2 * (s * s) ≤ N) :
    A s ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A s, ∀ b ∈ A s, Nat.lcm a b ≤ N := by
  have hss : ∀ i j, i ≤ s → j ≤ s → i * j ≤ s * s := fun i j hi hj => Nat.mul_le_mul hi hj
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Finset.mem_Icc]
    rcases mem_A hx with h | ⟨j, hj1, hj, rfl⟩
    · have := hss x 1 h.2 (by omega)
      omega
    · have := hss j 1 hj (by omega)
      omega
  · intro a ha b hb
    rcases mem_A ha with h | ⟨i, hi1, hi, rfl⟩ <;>
      rcases mem_A hb with h' | ⟨j, hj1, hj, rfl⟩
    · have := lcm_le_mul a b
      have := hss a b h.2 h'.2
      omega
    · have := lcm_le_mul a (2 * j)
      have := hss a j h.2 hj
      have e : a * (2 * j) = 2 * (a * j) := by ring
      omega
    · have := lcm_le_mul (2 * i) b
      have := hss i b hi h'.2
      have e : 2 * i * b = 2 * (i * b) := by ring
      omega
    · rw [Nat.lcm_mul_left]
      have := lcm_le_mul i j
      have := hss i j hi hj
      omega

lemma g_ge (N : ℕ) : Nat.sqrt (N / 2) + (Nat.sqrt (N / 2) - Nat.sqrt (N / 2) / 2) ≤ g N := by
  have h0 := Nat.sqrt_le' (N / 2)
  rw [pow_two] at h0
  set s := Nat.sqrt (N / 2)
  have hs : 2 * (s * s) ≤ N := by omega
  obtain ⟨h1, h2⟩ := good N s hs
  rw [← card_A]
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨B, hB, -, rfl⟩
    have := Finset.card_le_card hB
    rw [Nat.card_Icc] at this
    omega
  · exact ⟨A s, h1, h2, rfl⟩

end LB

theorem erdos_441.variants.lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, √(9 / 8 * N) - C ≤ g N := by
  refine ⟨3, fun N => ?_⟩
  have hg := LB.g_ge N
  have h1 := Nat.lt_succ_sqrt' (N / 2)
  rw [Nat.succ_eq_add_one, pow_two] at h1
  set s := Nat.sqrt (N / 2)
  have hN : N ≤ 2 * ((s + 2) * (s + 2)) := by
    have h2 : (s + 1) * (s + 1) ≤ (s + 2) * (s + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h3 : 3 * s ≤ 2 * (s + (s - s / 2)) := by omega
  have h3r : (3 : ℝ) * s ≤ 2 * ((s + (s - s / 2) : ℕ) : ℝ) := by exact_mod_cast h3
  have hgr : ((s + (s - s / 2) : ℕ) : ℝ) ≤ (g N : ℝ) := by exact_mod_cast hg
  have hNr : (N : ℝ) ≤ 2 * ((s + 2) * (s + 2)) := by exact_mod_cast hN
  have hsq : √(9 / 8 * (N : ℝ)) ≤ 3 / 2 * ((s : ℝ) + 2) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  linarith

end Erdos441

#print axioms Erdos441.erdos_441.variants.lower_bound
