import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace Erdos1052

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- All unitary divisors (including `n`). -/
def U (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- Sum of unitary divisors. -/
def S (n : ℕ) : ℕ := ∑ d ∈ U n, d

theorem mem_U {n d : ℕ} : d ∈ U n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp only [U, Finset.mem_filter, Nat.mem_divisors, and_assoc]

theorem S_eq {n : ℕ} (hn : 0 < n) : S n = ∑ i ∈ properUnitaryDivisors n, i + n := by
  have hnot : n ∉ properUnitaryDivisors n := by simp [properUnitaryDivisors]
  have hset : U n = insert n (properUnitaryDivisors n) := by
    ext d
    simp only [mem_U, properUnitaryDivisors, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_Ico]
    constructor
    · rintro ⟨hd, -, hc⟩
      by_cases hdn : d = n
      · exact Or.inl hdn
      · have h1 := Nat.pos_of_dvd_of_pos hd hn
        have h2 := Nat.le_of_dvd hn hd
        exact Or.inr ⟨⟨h1, by omega⟩, hd, hc⟩
    · rintro (h | ⟨-, hd, hc⟩)
      · subst h
        refine ⟨dvd_rfl, by omega, ?_⟩
        rw [Nat.div_self hn]; exact Nat.coprime_one_right _
      · exact ⟨hd, by omega, hc⟩
  rw [S, hset, Finset.sum_insert hnot, Nat.add_comm]

theorem S_mul {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    S (a * b) = S a * S b := by
  rw [S, S, S, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun x => x.1 * x.2) (fun f => (Nat.gcd f a, Nat.gcd f b))
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product, mem_U] at hxy ⊢
    obtain ⟨⟨hx, -, hcx⟩, ⟨hy, -, hcy⟩⟩ := hxy
    refine ⟨Nat.mul_dvd_mul hx hy, Nat.mul_ne_zero ha hb, ?_⟩
    rw [← Nat.div_mul_div_comm hx hy]
    have hxb : Nat.Coprime x (b / y) :=
      (hab.coprime_dvd_left hx).coprime_dvd_right (Nat.div_dvd_of_dvd hy)
    have hya : Nat.Coprime y (a / x) :=
      (hab.symm.coprime_dvd_left hy).coprime_dvd_right (Nat.div_dvd_of_dvd hx)
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    exact ⟨⟨hcx, hxb⟩, ⟨hya, hcy⟩⟩
  · intro f hf
    simp only [Finset.mem_product, mem_U] at hf ⊢
    obtain ⟨hf, -, hcf⟩ := hf
    have hfe : Nat.gcd f a * Nat.gcd f b = f := by
      rw [← Nat.Coprime.gcd_mul f hab]; exact Nat.gcd_eq_left hf
    have hq : a * b / f = (a / Nat.gcd f a) * (b / Nat.gcd f b) := by
      rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right f a) (Nat.gcd_dvd_right f b), hfe]
    rw [hq] at hcf
    refine ⟨⟨Nat.gcd_dvd_right f a, ha, ?_⟩, ⟨Nat.gcd_dvd_right f b, hb, ?_⟩⟩
    · exact (hcf.coprime_dvd_left (Nat.gcd_dvd_left f a)).coprime_dvd_right
        (dvd_mul_right _ _)
    · exact (hcf.coprime_dvd_left (Nat.gcd_dvd_left f b)).coprime_dvd_right
        (dvd_mul_left _ _)
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product, mem_U] at hxy
    obtain ⟨⟨hx, -, -⟩, ⟨hy, -, -⟩⟩ := hxy
    have hya : Nat.Coprime y a := hab.symm.coprime_dvd_left hy
    have hxb : Nat.Coprime x b := hab.coprime_dvd_left hx
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.Coprime.gcd_mul_right_cancel x hya]; exact Nat.gcd_eq_left hx
    · rw [Nat.Coprime.gcd_mul_left_cancel y hxb]; exact Nat.gcd_eq_left hy
  · intro f hf
    simp only [mem_U] at hf
    show Nat.gcd f a * Nat.gcd f b = f
    rw [← Nat.Coprime.gcd_mul f hab]; exact Nat.gcd_eq_left hf.1
  · intro x _; rfl

theorem S_pp {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) : S (p ^ a) = 1 + p ^ a := by
  have h1 : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
  have hset : U (p ^ a) = {1, p ^ a} := by
    ext d
    simp only [mem_U, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -, hc⟩
      obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
      rw [Nat.pow_div hb hp.pos] at hc
      by_cases hb0 : b = 0
      · left; simp [hb0]
      by_cases hba : b = a
      · right; rw [hba]
      exfalso
      have hpp : Nat.Coprime p p :=
        (hc.coprime_dvd_left (dvd_pow_self p hb0)).coprime_dvd_right
          (dvd_pow_self p (by omega))
      rw [Nat.Coprime, Nat.gcd_self] at hpp
      exact hp.one_lt.ne' hpp
    · rintro (h | h)
      · subst h
        exact ⟨one_dvd _, pow_ne_zero _ hp.ne_zero, Nat.coprime_one_left _⟩
      · subst h
        refine ⟨dvd_rfl, pow_ne_zero _ hp.ne_zero, ?_⟩
        rw [Nat.div_self (by omega)]; exact Nat.coprime_one_right _
  rw [S, hset, Finset.sum_pair (by omega)]

theorem split (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    ∃ p a m : ℕ, p.Prime ∧ 1 ≤ a ∧ n = p ^ a * m ∧ Nat.Coprime (p ^ a) m := by
  have hp := Nat.minFac_prime h1
  refine ⟨n.minFac, n.factorization n.minFac, n / n.minFac ^ n.factorization n.minFac, hp,
    ?_, (Nat.ordProj_mul_ordCompl_eq_self n _).symm, (Nat.coprime_ordCompl hp h0).pow_left _⟩
  exact (hp.dvd_iff_one_le_factorization h0).mp (Nat.minFac_dvd n)

theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hsum, hpos⟩ := hn
  have hS : S n = 2 * n := by have := S_eq hpos; omega
  by_contra hodd
  have hodd' : ¬ 2 ∣ n := fun h => hodd (even_iff_two_dvd.mpr h)
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp [properUnitaryDivisors] at hsum
  obtain ⟨p, a, m, hp, ha, rfl, hcop⟩ := split n (by omega) hn1
  have hm0 : m ≠ 0 := by rintro rfl; simp at hpos
  rw [S_mul hcop (pow_ne_zero _ hp.ne_zero) hm0, S_pp hp ha] at hS
  have hq2 : 2 ∣ 1 + p ^ a := by
    have : ¬ 2 ∣ p ^ a := fun h => hodd' (dvd_trans h (dvd_mul_right _ _))
    omega
  by_cases hm1 : m = 1
  · subst hm1
    have hS1 : S 1 = 1 := by decide
    rw [hS1, Nat.mul_one, Nat.mul_one] at hS
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  · obtain ⟨r, b, k, hr, hb, hmk, hcop2⟩ := split m hm0 hm1
    have hk0 : k ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hmk; exact hm0 hmk
    have hS2 : S m = (1 + r ^ b) * S k := by
      rw [hmk, S_mul hcop2 (pow_ne_zero _ hr.ne_zero) hk0, S_pp hr hb]
    have hr2 : 2 ∣ 1 + r ^ b := by
      have hrd : r ^ b ∣ p ^ a * m := by
        rw [hmk]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
      have : ¬ 2 ∣ r ^ b := fun h => hodd' (dvd_trans h hrd)
      omega
    have h4 : 4 ∣ (1 + p ^ a) * S m := by
      rw [hS2]
      obtain ⟨u, hu⟩ := hq2
      obtain ⟨v, hv⟩ := hr2
      rw [hu, hv]
      exact ⟨u * (v * S k), by ring⟩
    rw [hS] at h4
    generalize p ^ a * m = N at h4 hodd'
    omega

end Erdos1052

#print axioms Erdos1052.even_of_isUnitaryPerfect
