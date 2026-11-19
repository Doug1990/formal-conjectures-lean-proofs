import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Set

/-- (local copy of FormalConjecturesForMathlib/NumberTheory/Primitive.lean) -/
def IsPrimitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

end Set

namespace OeisA63880

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

namespace P

lemma U_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    unitaryDivisors (a * b) =
      (unitaryDivisors a ×ˢ unitaryDivisors b).image (fun x => x.1 * x.2) := by
  ext d
  simp only [unitaryDivisors, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
    Nat.mem_divisors, Prod.exists]
  constructor
  · rintro ⟨⟨hd, -⟩, hc⟩
    have hdd : d = d.gcd a * d.gcd b := by
      rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hd]
    have h1 : d.gcd a ∣ a := Nat.gcd_dvd_right d a
    have h2 : d.gcd b ∣ b := Nat.gcd_dvd_right d b
    have hq : a * b / d = (a / d.gcd a) * (b / d.gcd b) := by
      rw [Nat.div_mul_div_comm h1 h2, ← hdd]
    rw [hq] at hc
    refine ⟨d.gcd a, d.gcd b, ⟨⟨⟨h1, ha.ne'⟩, ?_⟩, ⟨⟨h2, hb.ne'⟩, ?_⟩⟩, hdd.symm⟩
    · exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d a)
        (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right _ _) hc)
    · exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d b)
        (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left _ _) hc)
  · rintro ⟨x, y, ⟨⟨⟨hx, -⟩, hxc⟩, ⟨⟨hy, -⟩, hyc⟩⟩, rfl⟩
    refine ⟨⟨Nat.mul_dvd_mul hx hy, (Nat.mul_pos ha hb).ne'⟩, ?_⟩
    rw [← Nat.div_mul_div_comm hx hy]
    have hxb : x.Coprime (b / y) := Nat.Coprime.coprime_dvd_left hx
      (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hy) hab)
    have hya : y.Coprime (a / x) := Nat.Coprime.coprime_dvd_left hy
      (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hx) hab.symm)
    exact Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_mul_iff_right.2 ⟨hxc, hxb⟩,
      Nat.coprime_mul_iff_right.2 ⟨hya, hyc⟩⟩

lemma usigma_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    usigma (a * b) = usigma a * usigma b := by
  unfold usigma
  rw [U_mul ha hb hab, Finset.sum_image (fun x hx y hy hxy => ?_), Finset.sum_product,
    Finset.sum_mul_sum]
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, unitaryDivisors,
    Finset.mem_filter, Nat.mem_divisors] at hx hy
  have hx2a : Nat.Coprime x.2 a := Nat.Coprime.coprime_dvd_left hx.2.1.1 hab.symm
  have hy2a : Nat.Coprime y.2 a := Nat.Coprime.coprime_dvd_left hy.2.1.1 hab.symm
  have hx1b : Nat.Coprime x.1 b := Nat.Coprime.coprime_dvd_left hx.1.1.1 hab
  have hy1b : Nat.Coprime y.1 b := Nat.Coprime.coprime_dvd_left hy.1.1.1 hab
  have e1 : x.1 = y.1 := by
    have h1 : Nat.gcd (x.1 * x.2) a = x.1 := by
      rw [Nat.Coprime.gcd_mul_right_cancel x.1 hx2a, Nat.gcd_eq_left hx.1.1.1]
    have h2 : Nat.gcd (y.1 * y.2) a = y.1 := by
      rw [Nat.Coprime.gcd_mul_right_cancel y.1 hy2a, Nat.gcd_eq_left hy.1.1.1]
    rw [← h1, ← h2]
    exact congrArg (fun t => Nat.gcd t a) hxy
  have e2 : x.2 = y.2 := by
    have h1 : Nat.gcd (x.1 * x.2) b = x.2 := by
      rw [Nat.Coprime.gcd_mul_left_cancel x.2 hx1b, Nat.gcd_eq_left hx.2.1.1]
    have h2 : Nat.gcd (y.1 * y.2) b = y.2 := by
      rw [Nat.Coprime.gcd_mul_left_cancel y.2 hy1b, Nat.gcd_eq_left hy.2.1.1]
    rw [← h1, ← h2]
    exact congrArg (fun t => Nat.gcd t b) hxy
  exact Prod.ext e1 e2

lemma U_pp {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) : usigma (p ^ j) = 1 + p ^ j := by
  have h : unitaryDivisors (p ^ j) = {1, p ^ j} := by
    ext d
    simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · left; rw [h0, pow_zero]
      · right
        by_contra hne
        have hij : i < j := lt_of_le_of_ne hi (fun h => hne (by rw [h]))
        rw [Nat.pow_div hi hp.pos] at hc
        have h3 := (Nat.coprime_pow_left_iff h0 _ _).1 hc
        have h4 := (Nat.coprime_pow_right_iff (by omega) _ _).1 h3
        exact hp.one_lt.ne' ((Nat.coprime_self _).1 h4)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, (pow_pos hp.pos j).ne'⟩, Nat.coprime_one_left _⟩
      · refine ⟨⟨dvd_rfl, (pow_pos hp.pos j).ne'⟩, ?_⟩
        rw [Nat.div_self (pow_pos hp.pos j)]
        exact Nat.coprime_one_right _
  unfold usigma
  rw [h, Finset.sum_pair (Nat.one_lt_pow (by omega) hp.one_lt).ne]

lemma U_one : usigma 1 = 1 := by decide

lemma usigma_pos {n : ℕ} (hn : 0 < n) : 0 < usigma n := by
  have h1 : 1 ∈ unitaryDivisors n := by
    simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, hn.ne'⟩, Nat.coprime_one_left _⟩
  exact lt_of_lt_of_le one_pos (Finset.single_le_sum (f := fun d => d)
    (fun i _ => Nat.zero_le i) h1)

lemma sigma_pos' {n : ℕ} (hn : 0 < n) : 0 < σ 1 n := by
  rw [sigma_one_apply]
  exact lt_of_lt_of_le one_pos (Finset.single_le_sum (f := fun d => d)
    (fun i _ => Nat.zero_le i) (Nat.one_mem_divisors.2 hn.ne'))

lemma geom (c : ℕ) : ∀ n : ℕ, (∑ k ∈ Finset.range n, (c + 1) ^ k) * c + 1 = (c + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_mul, add_right_comm, geom c n, pow_succ]
    ring

lemma core_le (c X Y A B : ℕ) (hX : X * c + 1 = (c + 1) * A) (hY : Y * c + 1 = (c + 1) * B)
    (hAB : A ≤ B) (hc : 0 < c) : X * (1 + B) ≤ Y * (1 + A) := by
  have h1 : (X * c + 1) * (1 + B) = (c + 1) * A * (1 + B) := by rw [hX]
  have h2 : (Y * c + 1) * (1 + A) = (c + 1) * B * (1 + A) := by rw [hY]
  by_contra h
  push Not at h
  have h3 := mul_lt_mul_of_pos_left h hc
  nlinarith [Nat.zero_le c]

lemma core_lt (c X Y A B : ℕ) (hX : X * c + 1 = (c + 1) * A) (hY : Y * c + 1 = (c + 1) * B)
    (hAB : A < B) : X * (1 + B) < Y * (1 + A) := by
  have h1 : (X * c + 1) * (1 + B) = (c + 1) * A * (1 + B) := by rw [hX]
  have h2 : (Y * c + 1) * (1 + A) = (c + 1) * B * (1 + A) := by rw [hY]
  by_contra h
  push Not at h
  have h3 := mul_le_mul_of_nonneg_left h (Nat.zero_le c)
  nlinarith [Nat.zero_le c]

lemma core0_le (c Y B : ℕ) (hY : Y * c + 1 = (c + 1) * B) (hB : c + 1 ≤ B) (hc : 0 < c) :
    1 + B ≤ Y := by
  by_contra h
  push Not at h
  have h3 := mul_lt_mul_of_pos_left h hc
  nlinarith

lemma core0_lt (c Y B : ℕ) (hY : Y * c + 1 = (c + 1) * B) (hB : c + 1 < B) :
    1 + B < Y := by
  by_contra h
  push Not at h
  have h3 := mul_le_mul_of_nonneg_left h (Nat.zero_le c)
  nlinarith

lemma pp_le {p j e : ℕ} (hp : p.Prime) (hje : j ≤ e) (he : 1 ≤ e) :
    σ 1 (p ^ j) * usigma (p ^ e) ≤ σ 1 (p ^ e) * usigma (p ^ j) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hc : 0 < c := by have := hp.two_le; omega
  have hY := geom c (e + 1)
  rw [← sigma_one_apply_prime_pow hp, pow_succ'] at hY
  rw [U_pp hp he]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, isMultiplicative_sigma.map_one, U_one, one_mul, mul_one]
    exact core0_le c _ _ hY (Nat.le_self_pow (by omega) _) hc
  · rw [U_pp hp hj]
    have hX := geom c (j + 1)
    rw [← sigma_one_apply_prime_pow hp, pow_succ'] at hX
    exact core_le c _ _ _ _ hX hY (Nat.pow_le_pow_right hp.pos hje) hc

lemma pp_lt {p j e : ℕ} (hp : p.Prime) (hje : j < e) (he : 2 ≤ e) :
    σ 1 (p ^ j) * usigma (p ^ e) < σ 1 (p ^ e) * usigma (p ^ j) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hY := geom c (e + 1)
  rw [← sigma_one_apply_prime_pow hp, pow_succ'] at hY
  rw [U_pp hp (by omega)]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, isMultiplicative_sigma.map_one, U_one, one_mul, mul_one]
    have hB : c + 1 < (c + 1) ^ e := by
      have := Nat.pow_lt_pow_right hp.one_lt (show 1 < e by omega)
      rwa [pow_one] at this
    exact core0_lt c _ _ hY hB
  · rw [U_pp hp hj]
    have hX := geom c (j + 1)
    rw [← sigma_one_apply_prime_pow hp, pow_succ'] at hX
    exact core_lt c _ _ _ _ hX hY (Nat.pow_lt_pow_right hp.one_lt hje)

theorem gen_le : ∀ m, 0 < m → ∀ d, d ∣ m → σ 1 d * usigma m ≤ σ 1 m * usigma d := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ d hd
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    exact pp_le hp hj hn
  | zero => intro h; omega
  | one => intro _ d hd; rw [Nat.dvd_one.1 hd]
  | coprime a b ha hb hab iha ihb =>
    intro _ d hd
    have hdd : d = d.gcd a * d.gcd b := by
      rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hd]
    have h12 : (d.gcd a).Coprime (d.gcd b) := Nat.Coprime.coprime_dvd_left
      (Nat.gcd_dvd_right _ _) (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) hab)
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos (by omega) (by omega))
    have hd1 : 0 < d.gcd a := Nat.gcd_pos_of_pos_left _ hd0
    have hd2 : 0 < d.gcd b := Nat.gcd_pos_of_pos_left _ hd0
    have h1 := iha (by omega) _ (Nat.gcd_dvd_right d a)
    have h2 := ihb (by omega) _ (Nat.gcd_dvd_right d b)
    rw [hdd, isMultiplicative_sigma.map_mul_of_coprime h12,
      isMultiplicative_sigma.map_mul_of_coprime hab, usigma_mul (by omega) (by omega) hab,
      usigma_mul hd1 hd2 h12]
    calc σ 1 (d.gcd a) * σ 1 (d.gcd b) * (usigma a * usigma b)
        = (σ 1 (d.gcd a) * usigma a) * (σ 1 (d.gcd b) * usigma b) := by ring
      _ ≤ (σ 1 a * usigma (d.gcd a)) * (σ 1 b * usigma (d.gcd b)) := Nat.mul_le_mul h1 h2
      _ = _ := by ring

theorem gen_lt {m d p : ℕ} (hm : 0 < m) (hd : d ∣ m) (hp : p.Prime)
    (hlt : d.factorization p < m.factorization p) (h2 : 2 ≤ m.factorization p) :
    σ 1 d * usigma m < σ 1 m * usigma d := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  have hmd := Nat.ordProj_mul_ordCompl_eq_self m p
  have hdd := Nat.ordProj_mul_ordCompl_eq_self d p
  have hcm : Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hm.ne')
  have hcd : Nat.Coprime (p ^ d.factorization p) (d / p ^ d.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hd0.ne')
  have hk : d / p ^ d.factorization p ∣ m / p ^ m.factorization p :=
    Nat.ordCompl_dvd_ordCompl_of_dvd hd p
  have hk0 : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm.ne'
  have hd'0 : 0 < d / p ^ d.factorization p := Nat.ordCompl_pos p hd0.ne'
  have key1 := pp_lt hp hlt h2
  have key2 := gen_le _ hk0 _ hk
  have pos : 0 < σ 1 (d / p ^ d.factorization p) * usigma (m / p ^ m.factorization p) :=
    Nat.mul_pos (sigma_pos' hd'0) (usigma_pos hk0)
  generalize m / p ^ m.factorization p = k at *
  generalize d / p ^ d.factorization p = d' at *
  generalize m.factorization p = e at *
  generalize d.factorization p = j at *
  subst hmd hdd
  rw [isMultiplicative_sigma.map_mul_of_coprime hcd, isMultiplicative_sigma.map_mul_of_coprime hcm,
    usigma_mul (pow_pos hp.pos _) hk0 hcm, usigma_mul (pow_pos hp.pos _) hd'0 hcd]
  calc σ 1 (p ^ j) * σ 1 d' * (usigma (p ^ e) * usigma k)
      = (σ 1 (p ^ j) * usigma (p ^ e)) * (σ 1 d' * usigma k) := by ring
    _ < (σ 1 (p ^ e) * usigma (p ^ j)) * (σ 1 d' * usigma k) :=
        mul_lt_mul_of_pos_right key1 pos
    _ ≤ (σ 1 (p ^ e) * usigma (p ^ j)) * (σ 1 k * usigma d') :=
        mul_le_mul_of_nonneg_left key2 (Nat.zero_le _)
    _ = _ := by ring

theorem A_of_mul_prime' {m p : ℕ} (hm : 0 < m) (hA : A (m * p)) (hp : p.Prime)
    (hpm : ¬ p ∣ m) : A m := by
  have hc : m.Coprime p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have h := hA.2
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, usigma_mul hm hp.pos hc] at h
  have hsp : σ 1 p = 1 + p := by
    have := sigma_one_apply_prime_pow hp (i := 1)
    rw [pow_one] at this
    rw [this, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  have hup : usigma p = 1 + p := by
    have := U_pp hp (j := 1) le_rfl
    rwa [pow_one] at this
  rw [hsp, hup] at h
  refine ⟨hm, ?_⟩
  have h' : σ 1 m * (1 + p) = (2 * usigma m) * (1 + p) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h'

end P

/-- Non-primitive terms have the form $m \cdot s$ where $m$ is primitive and $s$ is
squarefree with $\gcd(m, s) = 1$. -/
theorem exists_primitive_of_a {n : ℕ} (h : A n) :
    ∃ m s, IsPrimitiveTerm m ∧ Squarefree s ∧ m.Coprime s ∧ n = m * s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hpw : ∃ p, p.Prime ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n
  · obtain ⟨p, hp, hpn, hp2⟩ := hpw
    obtain ⟨k, rfl⟩ := hpn
    have hk : 0 < k := Nat.pos_of_mul_pos_left h.1
    have hpk : ¬ p ∣ k := fun hd => hp2 (by rw [sq]; exact Nat.mul_dvd_mul_left p hd)
    have hAk : A k := P.A_of_mul_prime' hk (by rw [mul_comm]; exact h) hp hpk
    have hlt : k < p * k := by have := hp.two_le; nlinarith
    obtain ⟨m, s, hm, hs, hms, rfl⟩ := ih k hlt hAk
    refine ⟨m, s * p, hm, ?_, ?_, by ring⟩
    · have hsp : s.Coprime p := Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpk (Dvd.dvd.mul_left hd m)))
      exact (Nat.squarefree_mul hsp).2 ⟨hs, hp.prime.squarefree⟩
    · exact Nat.Coprime.mul_right hms (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpk (Dvd.dvd.mul_right hd s))))
  · push Not at hpw
    refine ⟨n, 1, ?_, squarefree_one, Nat.coprime_one_right _, (mul_one n).symm⟩
    refine ⟨h, ?_⟩
    rw [Set.disjoint_left]
    intro d hd hdA
    rw [Finset.mem_coe, Nat.mem_properDivisors] at hd
    have hdA' : A d := hdA
    obtain ⟨hdn, hdlt⟩ := hd
    have hn0 := h.1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn0
    have hex : ∃ p, d.factorization p ≠ n.factorization p := by
      by_contra hne
      push Not at hne
      exact (Nat.ne_of_lt hdlt) (Nat.eq_of_factorization_eq hd0.ne' hn0.ne' hne)
    obtain ⟨p, hpne⟩ := hex
    have hle : d.factorization p ≤ n.factorization p :=
      (Nat.factorization_le_iff_dvd hd0.ne' hn0.ne').2 hdn p
    have hlt' : d.factorization p < n.factorization p := lt_of_le_of_ne hle hpne
    have hpf : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 (by omega)
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpf
    have h2 : 2 ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn0.ne').1 (hpw p hp hpn)
    have key := P.gen_lt hn0 hdn hp hlt' h2
    rw [hdA'.2, h.2] at key
    have e : 2 * usigma d * usigma n = 2 * usigma n * usigma d := by ring
    rw [e] at key
    exact lt_irrefl _ key

end OeisA63880

#print axioms OeisA63880.P.gen_le
#print axioms OeisA63880.exists_primitive_of_a
