import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter

namespace Erdos282

noncomputable def greedyUnitFractionRem (A : Set ℕ) (x : ℚ) (t : ℕ) : ℚ :=
  if x ≤ 0 then 0 else
    let n := sInf { n | n ∈ A ∧ 1 / x ≤ n }
    let rem := x - 1 / n
    match t with
    | 0 => rem
    | t + 1 => greedyUnitFractionRem (A \ {n}) rem t

lemma zero_of_nonpos (A : Set ℕ) (x : ℚ) (t : ℕ) (hx : x ≤ 0) :
    greedyUnitFractionRem A x t = 0 := by
  unfold greedyUnitFractionRem
  rw [if_pos hx]

lemma step (A : Set ℕ) (x : ℚ) (hx : 0 < x) (t : ℕ) :
    greedyUnitFractionRem A x (t + 1) =
      greedyUnitFractionRem (A \ {sInf { n | n ∈ A ∧ 1 / x ≤ n }})
        (x - 1 / (sInf { n | n ∈ A ∧ 1 / x ≤ n } : ℕ)) t := by
  conv_lhs => unfold greedyUnitFractionRem
  rw [if_neg (not_le.2 hx)]

lemma sInf_eq (A : Set ℕ) (x : ℚ) (hA : ∀ n : ℕ, 1 / x ≤ n → n ∈ A) :
    sInf { n | n ∈ A ∧ 1 / x ≤ n } = ⌈1 / x⌉₊ := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨hA _ (Nat.le_ceil _), Nat.le_ceil _⟩
  · exact le_csInf ⟨_, hA _ (Nat.le_ceil _), Nat.le_ceil _⟩ fun n hn => Nat.ceil_le.2 hn.2

theorem main : ∀ k : ℕ, ∀ (q : ℕ) (A : Set ℕ) (x : ℚ), 0 < q → x = k / q → k < q →
    (0 < x → ∀ n : ℕ, 1 / x ≤ n → n ∈ A) →
    ∃ T, ∀ t ≥ T, greedyUnitFractionRem A x t = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro q A x hq hx hkq hA
  by_cases hx0 : x ≤ 0
  · exact ⟨0, fun t _ => zero_of_nonpos A x t hx0⟩
  rw [not_le] at hx0
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hx; linarith
    · exact h
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hS := sInf_eq A x (hA hx0)
  have hinv : 1 / x = (q : ℚ) / k := by rw [hx, one_div_div]
  have h1 : (q : ℚ) ≤ ⌈1 / x⌉₊ * k := by
    have := Nat.le_ceil (1 / x)
    rw [hinv] at this ⊢
    exact (div_le_iff₀ hkQ).1 this
  have h2 : ((⌈1 / x⌉₊ : ℕ) : ℚ) * k - k < q := by
    have := Nat.ceil_lt_add_one (one_div_pos.2 hx0).le
    rw [hinv] at this
    have h3 := (lt_div_iff₀ hkQ).1 (by linarith : ((⌈(q : ℚ) / k⌉₊ : ℕ) : ℚ) - 1 < q / k)
    rw [hinv]
    linarith [sub_one_mul ((⌈(q : ℚ) / k⌉₊ : ℕ) : ℚ) (k : ℚ)]
  generalize ⌈1 / x⌉₊ = N at hS h1 h2
  have hN1 : q ≤ N * k := by exact_mod_cast h1
  have hN2 : N * k < q + k := by
    have : ((N * k : ℕ) : ℚ) < q + k := by push_cast; linarith
    exact_mod_cast this
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; omega
    · exact h
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN0
  have hqN : q ≤ q * N := Nat.le_mul_of_pos_right q hN0
  have hx' : x - 1 / N = ((N * k - q : ℕ) : ℚ) / ((q * N : ℕ) : ℚ) := by
    rw [hx, Nat.cast_sub hN1]
    push_cast
    field_simp
  have hlt : x - 1 / N < 1 / N := by
    have h4 : ((N * k : ℕ) : ℚ) < 2 * q := by
      have : N * k < 2 * q := by omega
      exact_mod_cast this
    push_cast at h4
    have h5 : x < 2 / N := by
      rw [hx, div_lt_div_iff₀ hqQ hNQ]
      linarith
    have : (2 : ℚ) / N = 1 / N + 1 / N := by ring
    linarith
  have hA' : 0 < x - 1 / N → ∀ n : ℕ, 1 / (x - 1 / N) ≤ n → n ∈ A \ {N} := by
    intro hpos n hn
    have hNn : (N : ℚ) < n := by
      have := (lt_one_div hpos hNQ).1 hlt
      linarith
    have hxx : x - 1 / N < x := by
      have : (0 : ℚ) < 1 / N := one_div_pos.2 hNQ
      linarith
    have h6 : 1 / x < 1 / (x - 1 / N) := one_div_lt_one_div_of_lt hpos hxx
    refine ⟨hA hx0 n (by linarith), ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact lt_irrefl _ hNn
  generalize hb : q * N = b at hx' hqN
  generalize ha : N * k = a at hx' hN1 hN2
  obtain ⟨T, hT⟩ := ih (a - q) (by omega) b (A \ {N}) (x - 1 / N) (by omega) hx'
    (by omega) hA'
  refine ⟨T + 1, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [step A x hx0 s, hS]
  exact hT s (by omega)

theorem erdos_282.variants.fibonacci {x : ℚ} (hx : x ∈ Set.Ioo 0 1) :
    greedyUnitFractionRem .univ x =ᶠ[atTop] 0 := by
  obtain ⟨h0, h1⟩ := hx
  have hnum : 0 < x.num := Rat.num_pos.2 h0
  have hq : 0 < x.den := Nat.pos_of_ne_zero x.den_nz
  have hx' : x = ((x.num.toNat : ℕ) : ℚ) / ((x.den : ℕ) : ℚ) := by
    have : ((x.num.toNat : ℕ) : ℤ) = x.num := Int.toNat_of_nonneg hnum.le
    rw [show ((x.num.toNat : ℕ) : ℚ) = (((x.num.toNat : ℕ) : ℤ) : ℚ) from
      (Int.cast_natCast _).symm, this, Rat.num_div_den]
  have hkq : x.num.toNat < x.den := by
    have h := h1
    rw [hx', div_lt_one (by exact_mod_cast hq)] at h
    exact_mod_cast h
  obtain ⟨T, hT⟩ := main _ x.den Set.univ x hq hx' hkq (fun _ _ _ => Set.mem_univ _)
  exact Filter.eventually_atTop.2 ⟨T, hT⟩

end Erdos282

#print axioms Erdos282.erdos_282.variants.fibonacci
