import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Minimal

namespace Erdos872

noncomputable section

def IsPrimitive (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ∣ b

/-- Every element of `{2..n}` is comparable with some element of a maximal primitive set. -/
lemma comparable {n : ℕ} {A : Finset ℕ} (hA : Maximal (IsPrimitive n) A) (x : ℕ)
    (hx : x ∈ Finset.Icc 2 n) : ∃ a ∈ A, a ∣ x ∨ x ∣ a := by
  by_contra hne
  simp only [not_exists, not_and, not_or] at hne
  have hxA : x ∉ A := fun h => (hne x h).1 dvd_rfl
  have hP : IsPrimitive n (insert x A) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx
      · exact hA.1.1 hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with h1 | ha' <;>
        rcases Finset.mem_insert.1 hb with h2 | hb'
      · exact absurd (h1.trans h2.symm) hab
      · subst h1
        exact (hne b hb').2
      · subst h2
        exact (hne a ha').1
      · exact hA.1.2 a ha' b hb' hab
  exact hxA (hA.2 hP (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))

lemma big {n q r k m : ℕ} (hqk : n < q ^ (k + 1)) (hqr : q ≤ r) (hm : m ≠ 0) :
    n < q ^ k * r ^ m :=
  calc n < q ^ (k + 1) := hqk
    _ = q ^ k * q := pow_succ q k
    _ ≤ q ^ k * r := Nat.mul_le_mul_left _ hqr
    _ ≤ q ^ k * r ^ m := Nat.mul_le_mul_left _ (Nat.le_self_pow hm r)

lemma log_facts {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) :
    Nat.log q n ≠ 0 ∧ n < q ^ (Nat.log q n + 1) := by
  have h := Nat.lt_pow_succ_log_self hq.one_lt n
  refine ⟨?_, h⟩
  intro h0
  rw [h0] at h
  simp at h
  omega

lemma bad {n q r a : ℕ} (hq : q.Prime) (hr : r.Prime) (hqn : q ≤ n) (hrn : r ≤ n)
    (hne : q ≠ r) (ha : 2 ≤ a) (han : a ≤ n)
    (h1 : a ∣ q ^ Nat.log q n ∨ q ^ Nat.log q n ∣ a)
    (h2 : a ∣ r ^ Nat.log r n ∨ r ^ Nat.log r n ∣ a) : False := by
  obtain ⟨hk0, hk⟩ := log_facts hq hqn
  obtain ⟨hm0, hm⟩ := log_facts hr hrn
  have hcop : Nat.Coprime (q ^ Nat.log q n) (r ^ Nat.log r n) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).2 hne)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have h := Nat.dvd_gcd h1 h2
    rw [hcop] at h
    have := Nat.le_of_dvd Nat.one_pos h
    omega
  · have hrq : r ∣ q := hr.dvd_of_dvd_pow ((dvd_pow_self r hm0).trans (h2.trans h1))
    exact hne ((Nat.prime_dvd_prime_iff_eq hr hq).1 hrq).symm
  · have hqr : q ∣ r := hq.dvd_of_dvd_pow ((dvd_pow_self q hk0).trans (h1.trans h2))
    exact hne ((Nat.prime_dvd_prime_iff_eq hq hr).1 hqr)
  · have h := Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2)
    rcases le_total q r with hqr | hqr
    · have := big hk hqr hm0
      omega
    · have := big hm hqr hk0
      rw [Nat.mul_comm] at this
      omega

theorem erdos_872.variants.prime_question :
    ∀ n ≥ 2, ∀ A : Finset ℕ, Maximal (IsPrimitive n) A →
      ((Finset.Icc 2 n).filter Nat.Prime).card ≤ A.card := by
  intro n hn A hA
  have key : ∀ q ∈ (Finset.Icc 2 n).filter Nat.Prime,
      ∃ a ∈ A, a ∣ q ^ Nat.log q n ∨ q ^ Nat.log q n ∣ a := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    apply comparable hA
    obtain ⟨hk0, -⟩ := log_facts hq.2 hq.1.2
    have h1 : q ≤ q ^ Nat.log q n := Nat.le_self_pow hk0 q
    have h2 : q ^ Nat.log q n ≤ n := Nat.pow_log_le_self q (by omega)
    simp only [Finset.mem_Icc]
    omega
  choose! f hfA hf using key
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro q hq
    exact hfA q hq
  · intro q hq r hr hqr
    by_contra hne
    have hq' := hq
    have hr' := hr
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hq' hr'
    have haA := hfA q hq
    have hmem := hA.1.1 haA
    simp only [Finset.mem_Icc] at hmem
    have h2 := hf r hr
    rw [← hqr] at h2
    exact bad hq'.2 hr'.2 hq'.1.2 hr'.1.2 hne hmem.1 hmem.2 (hf q hq) h2

end

end Erdos872

#print axioms Erdos872.erdos_872.variants.prime_question
