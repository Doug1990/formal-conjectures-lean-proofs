import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Set

/-- Local restatement of `Set.IsPrimitive` from FormalConjecturesForMathlib. -/
def IsPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

end Set

namespace OeisA63880

open scoped ArithmeticFunction.sigma

def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

theorem unitaryDivisors_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p) := by
  have hp0 : 0 < p := hp.pos
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.1 hd
    obtain ⟨t, rfl⟩ := hd₁
    have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
    rcases (Nat.dvd_prime hp).1 hd₂ with h2 | h2 <;> subst d₂
    · left
      rw [mul_one] at hcd ⊢
      have e : d₁ * t * p / d₁ = t * p := by
        rw [mul_assoc, Nat.mul_div_cancel_left _ hd₁0]
      rw [e] at hcd
      refine ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_right.1 hcd).1
    · right
      have e : d₁ * t * p / (d₁ * p) = t := by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]
      rw [e] at hcd
      refine ⟨d₁, ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩, rfl⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_left.1 hcd).1
  · rintro (⟨⟨hd, -⟩, hcd⟩ | ⟨d₁, ⟨⟨hd₁, -⟩, hcd⟩, rfl⟩)
    · obtain ⟨t, rfl⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd0] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) p, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd0]
      refine Nat.Coprime.mul_right hcd ?_
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_right d t))).symm
    · obtain ⟨t, rfl⟩ := hd₁
      have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd₁0] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right d₁ t) dvd_rfl, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [show d₁ * t * p / (d₁ * p) = t by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]]
      refine Nat.Coprime.mul_left hcd ?_
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_left t d₁))

theorem usigma_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    usigma (m * p) = usigma m * (p + 1) := by
  have hdisj : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * p)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.1 hd'
    have h1 : d₁ * p ∣ m := (Finset.mem_filter.1 hd).1 |> Nat.mem_divisors.1 |>.1
    exact hpm ((dvd_mul_left p d₁).trans h1)
  unfold usigma
  rw [unitaryDivisors_mul_prime hm hp hpm, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hp.pos h), ← Finset.sum_mul,
    mul_add, mul_one, add_comm]

theorem sigma_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    σ 1 (m * p) = σ 1 m * (p + 1) := by
  have hσp : σ 1 p = p + 1 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 1)
    simp [Finset.sum_range_succ] at this
    omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm, hσp]

theorem A_of_mul_prime {m p : ℕ} (hm : 0 < m) (hA : A (m * p)) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    A m := by
  refine ⟨hm, ?_⟩
  have h := hA.2
  rw [sigma_mul_prime hp hpm, usigma_mul_prime hm hp hpm, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

/-! ### Helpers (new) -/

namespace P

theorem U_mul_pow {m p a : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (ha : 0 < a) :
    unitaryDivisors (m * p ^ a) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p ^ a) := by
  have hq0 : 0 < p ^ a := pow_pos hp.pos a
  have hcop : ∀ x, x ∣ m → Nat.Coprime x (p ^ a) := fun x hx =>
    Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hpm (h.trans hx))).symm
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.1 hd
    obtain ⟨t, rfl⟩ := hd₁
    have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd₂
    have e : d₁ * t * p ^ a / (d₁ * p ^ j) = t * p ^ (a - j) := by
      have : d₁ * t * p ^ a = (d₁ * p ^ j) * (t * p ^ (a - j)) := by
        rw [show p ^ a = p ^ j * p ^ (a - j) by rw [← pow_add]; congr 1; omega]; ring
      rw [this, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 (pow_pos hp.pos j))]
    rw [e] at hcd
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      left
      rw [pow_zero, mul_one, Nat.sub_zero] at hcd
      rw [pow_zero, mul_one]
      refine ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_right.1 hcd).1
    · rcases eq_or_lt_of_le hj with hja | hja
      · subst hja
        right
        rw [Nat.sub_self, pow_zero, mul_one] at hcd
        refine ⟨d₁, ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩, rfl⟩
        rw [Nat.mul_div_cancel_left _ hd₁0]
        exact (Nat.coprime_mul_iff_left.1 hcd).1
      · exfalso
        have h1 : p ∣ d₁ * p ^ j := dvd_mul_of_dvd_right (dvd_pow_self p hj0.ne') _
        have h2 : p ∣ t * p ^ (a - j) := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
        have := Nat.dvd_gcd h1 h2
        rw [Nat.Coprime.gcd_eq_one hcd] at this
        exact hp.ne_one (Nat.dvd_one.1 this)
  · rintro (⟨⟨hd, -⟩, hcd⟩ | ⟨d₁, ⟨⟨hd₁, -⟩, hcd⟩, rfl⟩)
    · obtain ⟨t, rfl⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd0] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) _, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd0]
      exact Nat.Coprime.mul_right hcd (hcop d (dvd_mul_right d t))
    · obtain ⟨t, rfl⟩ := hd₁
      have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd₁0] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right d₁ t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [show d₁ * t * p ^ a / (d₁ * p ^ a) = t by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hq0)]]
      exact Nat.Coprime.mul_left hcd (hcop t (dvd_mul_left t d₁)).symm

theorem usigma_mul_pow {m p a : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (ha : 0 < a) :
    usigma (m * p ^ a) = usigma m * (1 + p ^ a) := by
  have hq0 : 0 < p ^ a := pow_pos hp.pos a
  have hdisj : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * p ^ a)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.1 hd'
    have h1 : d₁ * p ^ a ∣ m := (Finset.mem_filter.1 hd).1 |> Nat.mem_divisors.1 |>.1
    exact hpm ((dvd_pow_self p ha.ne').trans ((dvd_mul_left _ d₁).trans h1))
  unfold usigma
  rw [U_mul_pow hm hp hpm ha, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq0 h), ← Finset.sum_mul]
  ring

def u (p b : ℕ) : ℕ := if b = 0 then 1 else 1 + p ^ b

theorem u_pos (p b : ℕ) : 0 < u p b := by
  unfold u; split <;> omega

theorem usigma_mul_pow' {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (b : ℕ) :
    usigma (m * p ^ b) = usigma m * u p b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [u]
  · rw [usigma_mul_pow hm hp hpm hb, u, if_neg (by omega)]

theorem usigma_pos {n : ℕ} (hn : 0 < n) : 0 < usigma n := by
  have h1 : 1 ∈ unitaryDivisors n :=
    Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hn.ne', Nat.coprime_one_left _⟩
  exact lt_of_lt_of_le one_pos (Finset.single_le_sum (f := fun d => d)
    (fun i _ => Nat.zero_le i) h1)

theorem hS (p k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * p + 1 = (∑ i ∈ Finset.range (k + 1), p ^ i) + p ^ (k + 1) := by
  induction k with
  | zero => simp [add_comm]
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, Nat.add_right_comm, ih, pow_succ p (k + 1)]

theorem alg {p s t q r : ℕ} (hp : 2 ≤ p) (hqr : q < r) (hs : s * p + 1 = s + q * p)
    (ht : t * p + 1 = t + r * p) : s * (1 + r) < t * (1 + q) := by
  by_contra h
  have h' : (t : ℤ) * (1 + q) ≤ s * (1 + r) := by exact_mod_cast not_lt.1 h
  have hs' : (s : ℤ) * p + 1 = s + q * p := by exact_mod_cast hs
  have ht' : (t : ℤ) * p + 1 = t + r * p := by exact_mod_cast ht
  have hn : (0 : ℤ) ≤ ((p : ℤ) - 1) * ((s : ℤ) * (1 + r) - t * (1 + q)) :=
    mul_nonneg (by omega) (by linarith)
  have e : ((p : ℤ) - 1) * ((s : ℤ) * (1 + r) - t * (1 + q)) + ((p : ℤ) + 1) * ((r : ℤ) - q) = 0 := by
    linear_combination (1 + (r : ℤ)) * hs' - (1 + (q : ℤ)) * ht'
  have hpos : (0 : ℤ) < ((p : ℤ) + 1) * ((r : ℤ) - q) := mul_pos (by omega) (by omega)
  linarith

theorem alg0 {p t r : ℕ} (hp : 2 ≤ p) (hr : p < r) (ht : t * p + 1 = t + r * p) :
    1 + r < t := by
  by_contra h
  have h' : (t : ℤ) ≤ 1 + r := by exact_mod_cast not_lt.1 h
  have ht' : (t : ℤ) * p + 1 = t + r * p := by exact_mod_cast ht
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hn : (0 : ℤ) ≤ ((p : ℤ) - 1) * (1 + r - t) := mul_nonneg (by omega) (by linarith)
  have e : ((p : ℤ) - 1) * (1 + r - t) = p - r := by linear_combination -ht'
  have : (p : ℤ) < r := by exact_mod_cast hr
  linarith

theorem loc {p a b : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hba : b < a) :
    σ 1 (p ^ b) * (1 + p ^ a) < σ 1 (p ^ a) * u p b := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have ht : (∑ i ∈ Finset.range (a + 1), p ^ i) * p + 1 =
      (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ a * p := by rw [← pow_succ]; exact hS p a
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hu : u p 0 = 1 := by simp [u]
    rw [hu, mul_one, zero_add, Finset.sum_range_one, pow_zero, one_mul]
    refine alg0 hp.two_le ?_ ht
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  · rw [u, if_neg (by omega)]
    have hs : (∑ i ∈ Finset.range (b + 1), p ^ i) * p + 1 =
        (∑ i ∈ Finset.range (b + 1), p ^ i) + p ^ b * p := by rw [← pow_succ]; exact hS p b
    exact alg hp.two_le (Nat.pow_lt_pow_right hp.one_lt hba) hs ht

theorem loc_le {p a b : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hba : b ≤ a) :
    σ 1 (p ^ b) * (1 + p ^ a) ≤ σ 1 (p ^ a) * u p b := by
  rcases lt_or_eq_of_le hba with h | h
  · exact (loc hp ha h).le
  · subst h; rw [u, if_neg (by omega)]

theorem key : ∀ m, 0 < m → (∀ q, m.factorization q ≠ 1) → ∀ d, d ∣ m →
    σ 1 d * usigma m ≤ σ 1 m * usigma d ∧ (d ≠ m → σ 1 d * usigma m < σ 1 m * usigma d) := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih hm hf d hd
  rcases eq_or_ne m 1 with rfl | hm1
  · have : d = 1 := Nat.dvd_one.1 hd
    subst this
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  have hp : m.minFac.Prime := Nat.minFac_prime hm1
  generalize hpdef : m.minFac = p at hp
  have hpm : p ∣ m := hpdef ▸ Nat.minFac_dvd m
  have ha1 : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hm.ne').1 hpm
  have ha : 2 ≤ m.factorization p := by have := hf p; omega
  have hm' : p ^ m.factorization p * ordCompl[p] m = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hm'0 : 0 < ordCompl[p] m := Nat.ordCompl_pos p hm.ne'
  have hpm' : ¬ p ∣ ordCompl[p] m := Nat.not_dvd_ordCompl hp hm.ne'
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hm.ne' (Nat.eq_zero_of_zero_dvd hd)
  have hd' : p ^ d.factorization p * ordCompl[p] d = d := Nat.ordProj_mul_ordCompl_eq_self d p
  have hd'0 : 0 < ordCompl[p] d := Nat.ordCompl_pos p hd0
  have hpd' : ¬ p ∣ ordCompl[p] d := Nat.not_dvd_ordCompl hp hd0
  have hd'm : ordCompl[p] d ∣ ordCompl[p] m := Nat.ordCompl_dvd_ordCompl_of_dvd hd p
  have hba : d.factorization p ≤ m.factorization p :=
    (Nat.factorization_le_iff_dvd hd0 hm.ne').2 hd p
  have hf' : ∀ q, (ordCompl[p] m).factorization q ≠ 1 := by
    intro q
    rw [Nat.factorization_ordCompl]
    by_cases hq : q = p
    · subst hq; simp
    · rw [Finsupp.erase_ne hq]; exact hf q
  generalize ordCompl[p] m = m' at *
  generalize ordCompl[p] d = d' at *
  generalize m.factorization p = a at *
  generalize d.factorization p = b at *
  have hlt : m' < m := by
    have h2 : 2 ≤ p ^ a := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    rw [← hm']; nlinarith
  obtain ⟨IH1, IH2⟩ := ih m' hlt hm'0 hf' d' hd'm
  have cop : ∀ x, ¬ p ∣ x → ∀ k, Nat.Coprime x (p ^ k) := fun x hx k =>
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hx).symm
  have sm : σ 1 m = σ 1 m' * σ 1 (p ^ a) := by
    rw [← hm', mul_comm (p ^ a) m']
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cop m' hpm' a)
  have sd : σ 1 d = σ 1 d' * σ 1 (p ^ b) := by
    rw [← hd', mul_comm (p ^ b) d']
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cop d' hpd' b)
  have um : usigma m = usigma m' * (1 + p ^ a) := by
    rw [← hm', mul_comm (p ^ a) m']
    exact usigma_mul_pow hm'0 hp hpm' (by omega)
  have ud : usigma d = usigma d' * u p b := by
    rw [← hd', mul_comm (p ^ b) d']
    exact usigma_mul_pow' hd'0 hp hpd' b
  have pos1 : 0 < σ 1 m' * usigma d' :=
    Nat.mul_pos (ArithmeticFunction.sigma_pos 1 m' hm'0.ne') (usigma_pos hd'0)
  have pos2 : 0 < σ 1 (p ^ a) * u p b :=
    Nat.mul_pos (ArithmeticFunction.sigma_pos 1 _ (pow_pos hp.pos a).ne') (u_pos p b)
  have e1 : σ 1 d * usigma m = (σ 1 d' * usigma m') * (σ 1 (p ^ b) * (1 + p ^ a)) := by
    rw [sd, um]; ring
  have e2 : σ 1 m * usigma d = (σ 1 m' * usigma d') * (σ 1 (p ^ a) * u p b) := by
    rw [sm, ud]; ring
  rw [e1, e2]
  refine ⟨Nat.mul_le_mul IH1 (loc_le hp ha hba), fun hne => ?_⟩
  by_cases h1 : d' = m'
  · have hb : b < a := by
      rcases lt_or_eq_of_le hba with h | h
      · exact h
      · exfalso; apply hne; rw [← hd', ← hm', h1, h]
    exact Nat.mul_lt_mul_of_le_of_lt IH1 (loc hp ha hb) pos1
  · exact Nat.mul_lt_mul_of_lt_of_le (IH2 h1) (loc_le hp ha hba) pos2

theorem prim {n : ℕ} (hA : A n) (hpow : ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) :
    IsPrimitiveTerm n := by
  refine ⟨hA, Set.disjoint_left.2 ?_⟩
  intro d hd hAd
  have hAd' : A d := hAd
  have hd' := Nat.mem_properDivisors.1 (Finset.mem_coe.1 hd)
  have hf : ∀ q, n.factorization q ≠ 1 := by
    intro q hq
    have hq' : q ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, hq]; omega
    have hqp := Nat.prime_of_mem_primeFactors hq'
    have := (hqp.pow_dvd_iff_le_factorization hA.1.ne').1
      (hpow q hqp (Nat.dvd_of_mem_primeFactors hq'))
    omega
  have := (key n hA.1 hf d hd'.1).2 hd'.2.ne
  rw [hA.2, hAd'.2] at this
  have e : 2 * usigma d * usigma n = 2 * usigma n * usigma d := by ring
  rw [e] at this
  exact lt_irrefl _ this

end P

theorem exists_primitive_of_a {n : ℕ} (h : A n) :
    ∃ m s, IsPrimitiveTerm m ∧ Squarefree s ∧ m.Coprime s ∧ n = m * s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hex : ∃ p, p.Prime ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n
  · obtain ⟨p, hp, hpn, hp2⟩ := hex
    obtain ⟨k, rfl⟩ := hpn
    have hk : 0 < k := Nat.pos_of_mul_pos_left h.1
    have hpk : ¬ p ∣ k := fun hd => hp2 (by rw [sq]; exact Nat.mul_dvd_mul_left p hd)
    have hAk : A k := A_of_mul_prime hk (by rw [mul_comm]; exact h) hp hpk
    have hlt : k < p * k := by have := hp.two_le; nlinarith
    obtain ⟨m, s, hm, hs, hms, rfl⟩ := ih k hlt hAk
    refine ⟨m, s * p, hm, ?_, ?_, by ring⟩
    · have hps : ¬ p ∣ s := fun hd => hpk (dvd_mul_of_dvd_right hd m)
      exact Nat.squarefree_mul_iff.2
        ⟨((Nat.Prime.coprime_iff_not_dvd hp).2 hps).symm, hs, (Nat.prime_iff.1 hp).squarefree⟩
    · exact Nat.Coprime.mul_right hms
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpk (dvd_mul_of_dvd_left hd s))).symm
  · push Not at hex
    exact ⟨n, 1, P.prim h hex, squarefree_one, Nat.coprime_one_right n, (mul_one n).symm⟩

end OeisA63880

#print axioms OeisA63880.exists_primitive_of_a
