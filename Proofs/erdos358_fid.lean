import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

namespace Erdos358

open Finset

def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

lemma mem_iff (n u v : ℕ) :
    (u, v) ∈ intervalRepresentations id n ↔ 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, i := Iff.rfl

lemma gauss (u k : ℕ) : (∑ i ∈ Icc u (u + k), i) * 2 = (k + 1) * (2 * u + k) := by
  induction k with
  | zero => rw [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton]; ring
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

lemma sum_eq (u v : ℕ) (huv : u ≤ v) : (∑ i ∈ Icc u v, i) * 2 = (v - u + 1) * (u + v) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  rw [gauss]
  congr 1 <;> omega

lemma rep {n u v p q : ℕ} (huv : u ≤ v) (h1 : v - u + 1 = p) (h2 : u + v = q)
    (hn : 2 * n = p * q) : n = ∑ i ∈ Icc u v, i := by
  have := sum_eq u v huv
  rw [h1, h2, ← hn] at this
  omega

def phi (n d : ℕ) : ℕ × ℕ :=
  (((d - 2 * (n / d)) + (2 * (n / d) - d) + 1) / 2, (d + 2 * (n / d) - 1) / 2)

lemma phi_mem {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (ho : Odd d) :
    phi n d ∈ intervalRepresentations id n := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨a, rfl⟩ := ho
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hq : n / (2 * a + 1) = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
  unfold phi
  rw [hq, mem_iff]
  refine ⟨by omega, by omega, ?_⟩
  rcases Nat.lt_or_ge (2 * m) (2 * a + 1) with h | h
  · exact rep (p := 2 * m) (q := 2 * a + 1) (by omega) (by omega) (by omega) (by rw [hm]; ring)
  · exact rep (p := 2 * a + 1) (q := 2 * m) (by omega) (by omega) (by omega) (by rw [hm]; ring)

lemma exists_d {n u v : ℕ} (hn : 0 < n) (h : (u, v) ∈ intervalRepresentations id n) :
    ∃ d ∈ n.divisors.filter (fun d => Odd d), phi n d = (u, v) := by
  rw [mem_iff] at h
  obtain ⟨hu, hv, hs⟩ := h
  have huv : u ≤ v := by
    by_contra hc
    rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hs
    omega
  have he := sum_eq u v huv
  rw [← hs] at he
  rcases Nat.even_or_odd (v - u + 1) with ⟨m, hm⟩ | ⟨c, hc⟩
  · have hnd : n = (u + v) * m := by
      rw [hm] at he
      have : (m + m) * (u + v) = 2 * ((u + v) * m) := by ring
      omega
    have hq : n / (u + v) = m := by rw [hnd, Nat.mul_div_cancel_left _ (by omega)]
    refine ⟨u + v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨⟨m, hnd⟩, by omega⟩, ⟨m + u - 1, by omega⟩⟩
    · simp only [phi, hq, Prod.mk.injEq]
      constructor <;> omega
  · have hnd : n = (v - u + 1) * (c + u) := by
      rw [hc] at he
      have h2 : u + v = 2 * (c + u) := by omega
      rw [h2] at he
      have : (2 * c + 1) * (2 * (c + u)) = 2 * ((2 * c + 1) * (c + u)) := by ring
      rw [hc]
      omega
    have hq : n / (v - u + 1) = c + u := by rw [hnd, Nat.mul_div_cancel_left _ (by omega)]
    refine ⟨v - u + 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨⟨c + u, hnd⟩, by omega⟩, ⟨c, hc⟩⟩
    · simp only [phi, hq, Prod.mk.injEq]
      constructor <;> omega

theorem f_id : f id = fun n ↦ #{d ∈ n.divisors | Odd d} := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hinf : (intervalRepresentations id 0).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 2, 1)) ?_ ?_
      · intro a b h
        simpa using h
      · intro k
        rw [mem_iff]
        refine ⟨by omega, by omega, ?_⟩
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have := hinf.to_subtype
    rw [f, Nat.card_eq_zero_of_infinite]
    simp
  · have hset : intervalRepresentations id n =
        ↑((n.divisors.filter (fun d => Odd d)).image (phi n)) := by
      ext ⟨u, v⟩
      rw [Finset.mem_coe, Finset.mem_image]
      constructor
      · intro h
        exact exists_d hn h
      · rintro ⟨d, hd, he⟩
        rw [← he]
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        exact phi_mem hn hd.1.1 hd.2
    rw [f, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn]
    intro d hd d' hd' h
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd hd'
    obtain ⟨⟨⟨m, hm⟩, -⟩, ⟨a, rfl⟩⟩ := hd
    obtain ⟨⟨⟨m', hm'⟩, -⟩, ⟨b, rfl⟩⟩ := hd'
    have hq : n / (2 * a + 1) = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
    have hq' : n / (2 * b + 1) = m' := by rw [hm', Nat.mul_div_cancel_left _ (by omega)]
    simp only [phi, hq, hq', Prod.mk.injEq] at h
    omega

end Erdos358

#print axioms Erdos358.f_id
