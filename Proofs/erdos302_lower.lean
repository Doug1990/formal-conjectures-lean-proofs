import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open Filter Finset
open scoped Topology

namespace Erdos302

def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

/-- Membership predicate for Cambie's set. -/
def P (N x : ℕ) : Prop := (x % 2 = 1 ∧ 4 * x ≤ N) ∨ (N < 2 * x ∧ x ≤ N)

lemma odd_odd {a b c : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (h : b * c = a * (b + c)) :
    False := by
  have := congrArg Even h
  simp only [eq_iff_iff] at this
  rw [Nat.even_mul, Nat.even_mul, Nat.even_add] at this
  simp only [Nat.even_iff] at this
  omega

lemma key {N a b c : ℕ} (ha : P N a) (hb : P N b) (hc : P N c)
    (hb0 : 0 < b) (hc0 : 0 < c) (h : b * c = a * (b + c)) : False := by
  rcases ha with ⟨ha2, ha4⟩ | ⟨ha1, ha2⟩
  · rcases hb with ⟨hb2, -⟩ | ⟨hb1, hb2⟩
    · exact odd_odd ha2 hb2 h
    rcases hc with ⟨hc2, -⟩ | ⟨hc1, hc2⟩
    · exact odd_odd ha2 hc2 (by rw [mul_comm, add_comm]; exact h)
    -- both b, c big
    have e1 : N * b < 2 * c * b := Nat.mul_lt_mul_of_pos_right hc1 hb0
    have e2 : N * c < 2 * b * c := Nat.mul_lt_mul_of_pos_right hb1 hc0
    have e3 : 4 * a * (b + c) ≤ N * (b + c) := Nat.mul_le_mul_right _ ha4
    nlinarith
  · have hbN : b ≤ N := by rcases hb with ⟨-, h4⟩ | ⟨-, h4⟩ <;> omega
    have hcN : c ≤ N := by rcases hc with ⟨-, h4⟩ | ⟨-, h4⟩ <;> omega
    have e1 : b * c ≤ N * c := Nat.mul_le_mul_right _ hbN
    have e2 : b * c ≤ b * N := Nat.mul_le_mul_left _ hcN
    have e3 : N * (b + c) < 2 * a * (b + c) := Nat.mul_lt_mul_of_pos_right ha1 (by omega)
    nlinarith

/-- Cambie's set. -/
def cambie (N : ℕ) : Finset ℕ :=
  (Finset.range ((N / 4 + 1) / 2)).image (fun x => 2 * x + 1) ∪ Finset.Ioc (N / 2) N

lemma mem_cambie {N x : ℕ} (hx : x ∈ cambie N) : P N x ∧ 1 ≤ x ∧ x ≤ N := by
  unfold cambie at hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_range] at hk
    refine ⟨Or.inl ⟨by omega, by omega⟩, by omega, by omega⟩
  · rw [Finset.mem_Ioc] at h
    refine ⟨Or.inr ⟨by omega, by omega⟩, by omega, by omega⟩

lemma cambie_sub (N : ℕ) : cambie N ⊆ Finset.Icc 1 N := by
  intro x hx
  have := mem_cambie hx
  rw [Finset.mem_Icc]
  omega

lemma cambie_no (N : ℕ) : NoUnitFractionTriple (cambie N) := by
  intro a ha b hb c hc _ _ _ h
  obtain ⟨Pa, a1, -⟩ := mem_cambie ha
  obtain ⟨Pb, b1, -⟩ := mem_cambie hb
  obtain ⟨Pc, c1, -⟩ := mem_cambie hc
  have ha0 : (a : ℚ) ≠ 0 := by positivity
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hc0 : (c : ℚ) ≠ 0 := by positivity
  rw [div_add_div _ _ hb0 hc0, div_eq_div_iff ha0 (mul_ne_zero hb0 hc0)] at h
  have h' : ((b * c : ℕ) : ℚ) = ((a * (b + c) : ℕ) : ℚ) := by
    push_cast
    linear_combination h
  exact key Pa Pb Pc (by omega) (by omega) (by exact_mod_cast h')

lemma cambie_card (N : ℕ) : 5 * N ≤ 8 * (cambie N).card + 16 := by
  have hd : Disjoint ((Finset.range ((N / 4 + 1) / 2)).image (fun x => 2 * x + 1))
      (Finset.Ioc (N / 2) N) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h1
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ioc] at h2
    omega
  unfold cambie
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy),
    Finset.card_range, Nat.card_Ioc]
  omega

theorem erdos_302.variants.lower_five_eighths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  filter_upwards [eventually_ge_atTop M] with N hN
  have hle : (cambie N).card ≤ f N := (hf N).2 ⟨cambie N, cambie_sub N, cambie_no N, rfl⟩
  have h1 : (5 * N : ℝ) ≤ 8 * (f N : ℝ) + 16 := by
    have := (cambie_card N).trans (by omega : 8 * (cambie N).card + 16 ≤ 8 * f N + 16)
    exact_mod_cast this
  have h2 : 2 < ε * N := by
    have h3 : (M : ℝ) ≤ N := by exact_mod_cast hN
    have h4 : 2 < ε * M := by
      have := (div_lt_iff₀ hε).1 hM
      linarith
    nlinarith
  nlinarith

theorem erdos_302.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  intro h
  have hev := erdos_302.variants.lower_five_eighths f hf (1 / 16) (by norm_num)
  have : (9 : ℝ) / 16 ≤ 1 / 2 := by
    refine ge_of_tendsto h ?_
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    have hpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [le_div_iff₀ hpos]
    linarith
  norm_num at this

end Erdos302

#print axioms Erdos302.erdos_302.variants.lower_five_eighths
#print axioms Erdos302.erdos_302.parts.ii
