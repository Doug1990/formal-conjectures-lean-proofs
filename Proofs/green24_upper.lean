import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter

namespace Green24

noncomputable def max013AffineTranslates (n : ℕ) : ℕ :=
  sSup { k |
    ∃ A : Finset ℤ,
      A.card = n ∧
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
  }

namespace variants

noncomputable def gamma : ℝ :=
  limsup (fun n : ℕ => (max013AffineTranslates n : ℝ) / ((n : ℝ)^2)) atTop

/-- `g A t` = number of elements of `A` that are `≤ t`. -/
def g (A : Finset ℤ) (t : ℤ) : ℕ := (A.filter (· ≤ t)).card

lemma g_succ (A : Finset ℤ) (t : ℤ) : g A (t + 1) ≤ g A t + 1 := by
  unfold g
  calc (A.filter (· ≤ t + 1)).card ≤ (insert (t + 1) (A.filter (· ≤ t))).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : x = t + 1
        · exact Or.inl h
        · exact Or.inr ⟨hx.1, by omega⟩
    _ ≤ _ := Finset.card_insert_le _ _

lemma g_low (A : Finset ℤ) (t : ℤ) (ht : ∀ a ∈ A, t < a) : g A t = 0 := by
  unfold g
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx h
  have := ht x hx
  omega

lemma g_high (A : Finset ℤ) (t : ℤ) (ht : ∀ a ∈ A, a ≤ t) : g A t = A.card := by
  unfold g
  rw [Finset.filter_true_of_mem ht]

/-- Discrete intermediate value: a "median" threshold. -/
lemma median (A : Finset ℤ) (k : ℕ) (hk : k ≤ A.card) : ∃ t, g A t = k := by
  rcases A.eq_empty_or_nonempty with h | hne
  · subst h
    refine ⟨0, ?_⟩
    simp only [Finset.card_empty, Nat.le_zero] at hk
    subst hk
    simp [g]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ∀ a ∈ A, m < a := ⟨A.min' hne - 1, fun a ha => by
    have := A.min'_le a ha; omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ a ∈ A, a ≤ M := ⟨A.max' hne, fun a ha => A.le_max' a ha⟩
  have hex : ∃ i : ℕ, k ≤ g A (m + i) := by
    refine ⟨(M - m).toNat, ?_⟩
    rw [g_high A _ (fun a ha => by have := hM a ha; have := hm a ha; omega)]
    exact hk
  classical
  let i₀ := Nat.find hex
  have hi₀ : k ≤ g A (m + i₀) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos i₀ with h0 | hpos
  · refine ⟨m, ?_⟩
    rw [h0] at hi₀
    simp only [Nat.cast_zero, add_zero] at hi₀
    rw [g_low A m hm] at hi₀ ⊢
    omega
  · have hlt : ¬ k ≤ g A (m + ((i₀ - 1 : ℕ) : ℤ)) := Nat.find_min hex (by omega)
    have hs := g_succ A (m + ((i₀ - 1 : ℕ) : ℤ))
    have he : m + ((i₀ - 1 : ℕ) : ℤ) + 1 = m + (i₀ : ℤ) := by
      have : ((i₀ - 1 : ℕ) : ℤ) = (i₀ : ℤ) - 1 := by omega
      rw [this]; ring
    rw [he] at hs
    refine ⟨m + (i₀ : ℤ), ?_⟩
    omega

/-- The counted set. -/
def T (A : Finset ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)

lemma low_part (A : Finset ℤ) (t : ℤ) :
    ((T A).filter (fun p => p.2 ≤ t)).card ≤ (A.filter (· ≤ t)).card ^ 2 := by
  set L := A.filter (· ≤ t)
  rw [pow_two, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn
    (fun p : ℤ × ℤ => if p.1 < p.2 then p else (p.2, p.1 + 3 * (p.2 - p.1))) (fun p hp => ?_) ?_
  · obtain ⟨x, y⟩ := p
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hx, hy⟩, hne, hw⟩, hyt⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_product, L, Finset.mem_filter]
    split_ifs with h
    · exact ⟨⟨hx, by omega⟩, hy, hyt⟩
    · exact ⟨⟨hy, hyt⟩, hw, by omega⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨_, hne, _⟩, _⟩ := hp
    obtain ⟨⟨_, hne', _⟩, _⟩ := hp'
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact h
    · simp only [Prod.mk.injEq] at h; omega
    · simp only [Prod.mk.injEq] at h; omega
    · simp only [Prod.mk.injEq] at h
      simp only [Prod.mk.injEq]; omega

lemma high_part (A : Finset ℤ) (t : ℤ) :
    ((T A).filter (fun p => ¬ p.2 ≤ t)).card ≤ (A.filter (fun a => ¬ a ≤ t)).card ^ 2 := by
  set U := A.filter (fun a => ¬ a ≤ t)
  rw [pow_two, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn
    (fun p : ℤ × ℤ => if p.2 < p.1 then p else (p.2, p.1 + 3 * (p.2 - p.1))) (fun p hp => ?_) ?_
  · obtain ⟨x, y⟩ := p
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hx, hy⟩, hne, hw⟩, hyt⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_product, U, Finset.mem_filter]
    split_ifs with h
    · exact ⟨⟨hx, by omega⟩, hy, hyt⟩
    · exact ⟨⟨hy, hyt⟩, hw, by omega⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨_, hne, _⟩, _⟩ := hp
    obtain ⟨⟨_, hne', _⟩, _⟩ := hp'
    simp only at h
    split_ifs at h with h1 h2 h2
    · exact h
    · simp only [Prod.mk.injEq] at h; omega
    · simp only [Prod.mk.injEq] at h; omega
    · simp only [Prod.mk.injEq] at h
      simp only [Prod.mk.injEq]; omega

lemma card_T (A : Finset ℤ) : 2 * (T A).card ≤ A.card ^ 2 + 1 := by
  obtain ⟨t, ht⟩ := median A (A.card / 2) (Nat.div_le_self _ _)
  have hsplit : ((T A).filter (fun p => p.2 ≤ t)).card
      + ((T A).filter (fun p => ¬ p.2 ≤ t)).card = (T A).card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hA : (A.filter (fun a => a ≤ t)).card
      + (A.filter (fun a => ¬ a ≤ t)).card = A.card := by
    rw [Finset.card_filter_add_card_filter_not]
  have h1 := low_part A t
  have h2 := high_part A t
  unfold g at ht
  rw [ht] at h1 hA
  set n := A.card
  set u := (A.filter (fun a => ¬ a ≤ t)).card
  have hu : u = n - n / 2 := by omega
  rw [hu] at h2
  rw [← hsplit]
  generalize ((T A).filter (fun p => p.2 ≤ t)).card = a at h1 ⊢
  generalize ((T A).filter (fun p => ¬ p.2 ≤ t)).card = b at h2 ⊢
  clear_value n u
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · have e1 : n / 2 = k := by omega
    have e2 : n - n / 2 = k := by omega
    rw [e1] at h1
    rw [e2] at h2
    rw [hk]
    nlinarith
  · have e1 : n / 2 = k := by omega
    have e2 : n - n / 2 = k + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    rw [hk]
    nlinarith

lemma max_le (n : ℕ) : 2 * max013AffineTranslates n ≤ n ^ 2 + 1 := by
  have hne : { k | ∃ A : Finset ℤ, A.card = n ∧
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card }.Nonempty :=
    ⟨_, ⟨(Finset.range n).image (fun a : ℕ => (a : ℤ)), by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range], rfl⟩⟩
  have : max013AffineTranslates n ≤ (n ^ 2 + 1) / 2 := by
    apply csSup_le hne
    rintro k ⟨A, hA, rfl⟩
    have := card_T A
    rw [hA] at this
    unfold T at this
    omega
  omega

theorem upper_HL : gamma ≤ 3/4 := by
  unfold gamma
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · rw [eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    have h1 : (2 * max013AffineTranslates n : ℕ) ≤ n ^ 2 + 1 := max_le n
    have h1' : 2 * (max013AffineTranslates n : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by exact_mod_cast h1
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith

end variants

end Green24

#print axioms Green24.variants.upper_HL
