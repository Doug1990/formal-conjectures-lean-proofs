import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Nat.Prime.Infinite

/-! Erdos939.erdos_939.variants.infinite_of_six_le (ErdosProblems/939.lean:92) and
Erdos939.erdos_939.variants.finite (ErdosProblems/939.lean:77). -/

namespace Nat
/-- restated from FormalConjecturesForMathlib/Data/Nat/Full.lean -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n
end Nat

namespace Erdos939

namespace Q

/-- `a * b^r` is `r`-full when every prime factor of `a` divides `b`. -/
lemma full_of (r a b : ℕ) (h : ∀ p, p.Prime → p ∣ a → p ∣ b) : Nat.Full r (a * b ^ r) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, _⟩ := hp
  have hpb : p ∣ b := by
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h1 | h1
    · exact h p hpp h1
    · exact hpp.dvd_of_dvd_pow h1
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpb r) a

/-- (Y+X)^r = (X-Y)^r + Σ_{m odd} 2 C(r,m) Y^m X^(r-m), over ℤ. -/
lemma odd_binom (X Y : ℤ) (r : ℕ) :
    (Y + X) ^ r = (X - Y) ^ r +
      ∑ m ∈ (Finset.range (r + 1)).filter Odd, 2 * (Y ^ m * X ^ (r - m) * (r.choose m)) := by
  rw [add_pow, show X - Y = -Y + X by ring, add_pow, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rcases Nat.even_or_odd m with h | h
  · have h' : ¬ Odd m := Nat.not_odd_iff_even.mpr h
    rw [h.neg_pow, if_neg h']
    ring
  · rw [h.neg_pow, if_pos h]
    ring

lemma card_odd (n : ℕ) : ((Finset.range n).filter Odd).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      rw [Nat.odd_iff] at h
      omega
    · rw [ih]
      rw [Nat.not_odd_iff_even, Nat.even_iff] at h
      omega

lemma val (q a e : ℕ) (hq : q.Prime) (ha0 : a ≠ 0) (ha : ¬ q ∣ a) :
    (a * q ^ e).factorization q = e := by
  rw [Nat.factorization_mul ha0 (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ha, Nat.factorization_pow, Finsupp.smul_apply,
    hq.factorization_self]
  simp

lemma sq_le_four_pow (r : ℕ) : r * r ≤ 4 ^ r := by
  have h := Nat.lt_two_pow_self (n := r)
  have : (4 : ℕ) ^ r = 2 ^ r * 2 ^ r := by
    rw [← mul_pow]
    norm_num
  rw [this]
  exact Nat.mul_le_mul h.le h.le

lemma two_choose_le (r m : ℕ) (hr : 1 ≤ r) : 2 * r.choose m ≤ 4 ^ r := by
  have h1 := Nat.choose_le_two_pow r m
  have h2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have : (4 : ℕ) ^ r = 2 ^ r * 2 ^ r := by
    rw [← mul_pow]
    norm_num
  rw [this]
  exact Nat.mul_le_mul h2 h1

lemma gauss_le (k : ℕ) : ∑ i ∈ Finset.range k, (i + 1) ≤ k * k := by
  have := Finset.sum_le_card_nsmul (Finset.range k) (fun i => i + 1) k
    (fun i hi => by rw [Finset.mem_range] at hi; omega)
  simpa using this

def B (r : ℕ) : ℕ := (4 ^ r).factorial

def Sk (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (i + 1)

lemma dvdB (r m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 4 ^ r) : m ∣ B r := Nat.dvd_factorial h1 h2

lemma B_pos (r : ℕ) : 0 < B r := Nat.factorial_pos _

/-- the odd-index binomial summands -/
def T (r q m : ℕ) : ℕ := 2 * r.choose m * (B r ^ m * q ^ (r - m)) ^ r

lemma full_T (r q m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ r) : Nat.Full r (T r q m) := by
  unfold T
  refine full_of r _ _ (fun p hp hpd => ?_)
  have hc : 1 ≤ 2 * r.choose m := by
    have := Nat.choose_pos hmr
    omega
  have hB : p ∣ B r := dvd_trans hpd (dvdB r _ hc (two_choose_le r m hr))
  exact dvd_trans hB (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)

/-- the pieces of the `m = 3` summand -/
def P (r q k i : ℕ) : ℕ :=
  (i + 1) * (2 * r.choose 3) * (B r / Sk k) * B r ^ (2 * r - 1) * (B r * q ^ (r - 3)) ^ r

lemma full_P (r q k i : ℕ) (hr : 3 ≤ r) (hik : i < k) (hk : k ≤ r) (hS : Sk k ∣ B r) :
    Nat.Full r (P r q k i) := by
  unfold P
  refine full_of r _ _ (fun p hp hpd => ?_)
  have hpB : p ∣ B r := by
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have h4 := sq_le_four_pow r
          have : i + 1 ≤ r * r := by nlinarith
          exact dvd_trans h (dvdB r _ (by omega) (by omega))
        · have hc : 1 ≤ 2 * r.choose 3 := by
            have := Nat.choose_pos hr
            omega
          exact dvd_trans h (dvdB r _ hc (two_choose_le r 3 (by omega)))
      · exact dvd_trans h (Nat.div_dvd_of_dvd hS)
    · exact hp.dvd_of_dvd_pow h
  exact dvd_mul_of_dvd_left hpB _

lemma sum_P (r q k : ℕ) (hr : 3 ≤ r) (hS : Sk k ∣ B r) :
    ∑ i ∈ Finset.range k, P r q k i = T r q 3 := by
  unfold P
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change Sk k * _ * _ * _ * _ = _
  have e : B r * B r ^ (2 * r - 1) = B r ^ (2 * r) := by
    rw [← pow_succ']
    congr 1
    omega
  unfold T
  calc Sk k * (2 * r.choose 3) * (B r / Sk k) * B r ^ (2 * r - 1) * (B r * q ^ (r - 3)) ^ r
      = 2 * r.choose 3 * (Sk k * (B r / Sk k)) * B r ^ (2 * r - 1) *
          (B r * q ^ (r - 3)) ^ r := by ring
    _ = 2 * r.choose 3 * (B r * B r ^ (2 * r - 1)) * (B r * q ^ (r - 3)) ^ r := by
          rw [Nat.mul_div_cancel' hS]; ring
    _ = 2 * r.choose 3 * (B r ^ 3 * q ^ (r - 3)) ^ r := by rw [e]; ring

lemma cop (r q : ℕ) (hr : 1 ≤ r) (hq : q.Prime) (hqB : ¬ q ∣ B r) (hlt : B r ^ r < q ^ r) :
    Nat.Coprime ((q ^ r - B r ^ r) ^ r) (T r q 1) := by
  unfold T
  apply Nat.Coprime.pow_left
  apply Nat.coprime_of_dvd
  intro p hp h1 h2
  have hcase : p ∣ B r ∨ p = q := by
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · left
      exact dvd_trans h (dvdB r _ (by have := Nat.choose_pos (show 1 ≤ r from hr); omega)
        (two_choose_le r 1 hr))
    · have h' := hp.dvd_of_dvd_pow h
      rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · left
        simpa using h''
      · right
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h'')
  rcases hcase with hB | rfl
  · have hBr : p ∣ B r ^ r := dvd_pow hB (by omega)
    have hqr : p ∣ p ^ 0 * q ^ r := by
      rw [pow_zero, one_mul, ← Nat.sub_add_cancel hlt.le]
      exact dvd_add h1 hBr
    rw [pow_zero, one_mul] at hqr
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hqr)
    subst this
    exact hqB hB
  · have hpr : p ∣ p ^ r := dvd_pow_self p (by omega)
    have hd : p ∣ p ^ r - (p ^ r - B r ^ r) := Nat.dvd_sub hpr h1
    rw [Nat.sub_sub_self hlt.le] at hd
    exact hqB (hp.dvd_of_dvd_pow hd)

lemma not_dvd_small (q c : ℕ) (hc : 0 < c) (hcq : c < q) : ¬ q ∣ c :=
  fun h => absurd (Nat.le_of_dvd hc h) (by omega)

lemma not_dvd_Bpow (r q n : ℕ) (hq : q.Prime) (hqB : ¬ q ∣ B r) : ¬ q ∣ B r ^ n :=
  fun h => hqB (hq.dvd_of_dvd_pow h)

lemma T_eq (r q m : ℕ) :
    T r q m = (2 * r.choose m * B r ^ (m * r)) * q ^ ((r - m) * r) := by
  unfold T
  rw [mul_pow, ← pow_mul, ← pow_mul]
  ring

lemma val_T (r q m : ℕ) (hr : 1 ≤ r) (hmr : m ≤ r) (hq : q.Prime) (hqB : ¬ q ∣ B r)
    (hMq : 4 ^ r < q) : (T r q m).factorization q = (r - m) * r := by
  rw [T_eq]
  have hc : 0 < 2 * r.choose m := by have := Nat.choose_pos hmr; omega
  apply val q _ _ hq
  · exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (B_pos r).ne')
  · intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact not_dvd_small q _ hc (lt_of_le_of_lt (two_choose_le r m hr) hMq) h
    · exact not_dvd_Bpow r q _ hq hqB h

lemma P_eq (r q k i : ℕ) :
    P r q k i = ((i + 1) * (2 * r.choose 3) * (B r / Sk k) * B r ^ (2 * r - 1) * B r ^ r) *
      q ^ ((r - 3) * r) := by
  unfold P
  rw [mul_pow, ← pow_mul]
  ring

lemma val_P (r q k i : ℕ) (hr : 3 ≤ r) (hik : i < k) (hk : k ≤ r) (hS : Sk k ∣ B r)
    (hS0 : 0 < Sk k) (hq : q.Prime) (hqB : ¬ q ∣ B r) (hMq : 4 ^ r < q) :
    (P r q k i).factorization q = (r - 3) * r := by
  rw [P_eq]
  have hc : 0 < 2 * r.choose 3 := by have := Nat.choose_pos hr; omega
  have hBS : 0 < B r / Sk k := Nat.div_pos (Nat.le_of_dvd (B_pos r) hS) hS0
  have h4 := sq_le_four_pow r
  have hi : i + 1 < q := by nlinarith
  apply val q _ _ hq
  · refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega)
      (by omega)) (by omega)) (pow_ne_zero _ (B_pos r).ne')) (pow_ne_zero _ (B_pos r).ne')
  · intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · exact not_dvd_small q _ (by omega) hi h
          · exact not_dvd_small q _ hc (lt_of_le_of_lt (two_choose_le r 3 (by omega)) hMq) h
        · exact hqB (dvd_trans h (Nat.div_dvd_of_dvd hS))
      · exact not_dvd_Bpow r q _ hq hqB h
    · exact not_dvd_Bpow r q _ hq hqB h

/-! ## Assembly -/

lemma full_pow (r x : ℕ) : Nat.Full r (x ^ r) := by
  have h := full_of r 1 x (fun p hp h => absurd (Nat.le_of_dvd one_pos h)
    (by have := hp.two_le; omega))
  rwa [one_mul] at h

lemma four_le (r : ℕ) (hr : 1 ≤ r) : 4 ≤ 4 ^ r := by
  calc 4 = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hr

lemma le_B (r : ℕ) : 4 ^ r ≤ B r := Nat.self_le_factorial _

lemma two_dvd_B (r : ℕ) (hr : 1 ≤ r) : 2 ∣ B r :=
  dvdB r 2 (by norm_num) (by have := four_le r hr; omega)

lemma pow_lt (r q : ℕ) (hr : 1 ≤ r) (hq : B r < q) : B r ^ r < q ^ r :=
  Nat.pow_lt_pow_left hq (by omega)

lemma s0_odd (r q : ℕ) (hr : 1 ≤ r) (hq : q.Prime) (hBq : B r < q) :
    ¬ 2 ∣ (q ^ r - B r ^ r) ^ r := by
  intro h
  have h1 := Nat.prime_two.dvd_of_dvd_pow h
  have h2 : 2 ∣ B r ^ r := dvd_pow (two_dvd_B r hr) (by omega)
  have h3 : 2 ∣ q ^ r := by
    have := Nat.dvd_add h1 h2
    rwa [Nat.sub_add_cancel (pow_lt r q hr hBq).le] at this
  have h4 := Nat.prime_two.dvd_of_dvd_pow h3
  have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h4
  have := four_le r hr
  have := le_B r
  omega

lemma two_dvd_T (r q m : ℕ) : 2 ∣ T r q m := by
  unfold T
  exact (dvd_mul_right 2 _).mul_right _

lemma two_dvd_P (r q k i : ℕ) : 2 ∣ P r q k i := by
  unfold P
  exact (((dvd_trans (dvd_mul_right 2 _) (dvd_mul_left _ _)).mul_right _).mul_right _).mul_right _

lemma T_pos (r q m : ℕ) (hmr : m ≤ r) (hq0 : 0 < q) : 0 < T r q m := by
  unfold T
  apply Nat.pos_of_ne_zero
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (Nat.choose_pos hmr).ne')
    (pow_ne_zero _ (Nat.mul_ne_zero (pow_ne_zero _ (B_pos r).ne') (pow_ne_zero _ hq0.ne')))

lemma P_mul (r q k i : ℕ) : P r q k i = (i + 1) * P r q k 0 := by
  unfold P
  ring

lemma P0_pos (r q k : ℕ) (hr : 3 ≤ r) (hS : Sk k ∣ B r) (hS0 : 0 < Sk k) (hq0 : 0 < q) :
    0 < P r q k 0 := by
  unfold P
  apply Nat.pos_of_ne_zero
  refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) ?_) ?_) ?_) ?_
  · have := Nat.choose_pos hr
    omega
  · exact (Nat.div_pos (Nat.le_of_dvd (B_pos r) hS) hS0).ne'
  · exact pow_ne_zero _ (B_pos r).ne'
  · exact pow_ne_zero _ (Nat.mul_ne_zero (B_pos r).ne' (pow_ne_zero _ hq0.ne'))

lemma Sk_pos (k : ℕ) (hk : 1 ≤ k) : 0 < Sk k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold Sk
  rw [Finset.sum_range_succ]
  omega

lemma Sk_dvd (r k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ r) : Sk k ∣ B r :=
  dvdB r _ (Sk_pos k hk1)
    (le_trans (gauss_le k) (le_trans (Nat.mul_le_mul hk hk) (sq_le_four_pow r)))

def Modd (r : ℕ) : Finset ℕ := ((Finset.range (r + 1)).filter Odd).erase 3

lemma mem_Modd (r m : ℕ) (h : m ∈ Modd r) : m ≠ 3 ∧ m ≤ r ∧ Odd m := by
  simp only [Modd, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at h
  exact ⟨h.1, by omega, h.2.2⟩

lemma sum_eq (r q : ℕ) (hle : B r ^ r ≤ q ^ r) :
    (q ^ r - B r ^ r) ^ r + ∑ m ∈ (Finset.range (r + 1)).filter Odd, T r q m
      = (q ^ r + B r ^ r) ^ r := by
  have h := odd_binom ((q : ℤ) ^ r) ((B r : ℤ) ^ r) r
  have hT : ∀ m, ((T r q m : ℕ) : ℤ) =
      2 * (((B r : ℤ) ^ r) ^ m * ((q : ℤ) ^ r) ^ (r - m) * (r.choose m : ℤ)) := by
    intro m
    unfold T
    push_cast
    ring
  have key : (((q ^ r - B r ^ r) ^ r + ∑ m ∈ (Finset.range (r + 1)).filter Odd, T r q m : ℕ) : ℤ)
      = (((q ^ r + B r ^ r) ^ r : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_sub hle, Nat.cast_sum, hT]
    rw [add_comm ((q : ℤ) ^ r), h]
  exact Nat.cast_inj.mp key

/-- the solution set for the prime `q` -/
def S (r q : ℕ) : Finset ℕ :=
  insert ((q ^ r - B r ^ r) ^ r)
    ((Modd r).image (T r q) ∪ (Finset.range (r / 2 - 2)).image (P r q (r / 2 - 2)))

section
variable (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hBq : B r < q)
include hr hq hBq

omit hr hq in
lemma hMq : 4 ^ r < q := lt_of_le_of_lt (le_B r) hBq

lemma T_inj : Set.InjOn (T r q) (Modd r) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  have ha' := mem_Modd r a ha
  have hb' := mem_Modd r b hb
  have hqB : ¬ q ∣ B r := not_dvd_small q _ (B_pos r) hBq
  have h1 := val_T r q a (by omega) ha'.2.1 hq hqB (hMq r q hBq)
  have h2 := val_T r q b (by omega) hb'.2.1 hq hqB (hMq r q hBq)
  rw [hab] at h1
  have := Nat.eq_of_mul_eq_mul_right (show 0 < r by omega) (h1.symm.trans h2)
  omega

omit hBq in
lemma P_inj : Set.InjOn (P r q (r / 2 - 2)) (Finset.range (r / 2 - 2)) := by
  intro a _ b _ hab
  have hS := Sk_dvd r (r / 2 - 2) (by omega) (by omega)
  have hpos := P0_pos r q (r / 2 - 2) (by omega) hS (Sk_pos _ (by omega)) hq.pos
  rw [P_mul r q _ a, P_mul r q _ b] at hab
  have := Nat.eq_of_mul_eq_mul_right hpos hab
  omega

lemma disj : Disjoint ((Modd r).image (T r q))
    ((Finset.range (r / 2 - 2)).image (P r q (r / 2 - 2))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨i, hi, he⟩ := hx'
  have hm' := mem_Modd r m hm
  have hqB : ¬ q ∣ B r := not_dvd_small q _ (B_pos r) hBq
  have hS := Sk_dvd r (r / 2 - 2) (by omega) (by omega)
  have h1 := val_T r q m (by omega) hm'.2.1 hq hqB (hMq r q hBq)
  have h2 := val_P r q (r / 2 - 2) i (by omega) (Finset.mem_range.mp hi) (by omega) hS
    (Sk_pos _ (by omega)) hq hqB (hMq r q hBq)
  rw [he] at h2
  have := Nat.eq_of_mul_eq_mul_right (show 0 < r by omega) (h1.symm.trans h2)
  exact hm'.1 (by omega)

lemma notMem : (q ^ r - B r ^ r) ^ r ∉
    ((Modd r).image (T r q) ∪ (Finset.range (r / 2 - 2)).image (P r q (r / 2 - 2))) := by
  intro h
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at h
  apply s0_odd r q (by omega) hq hBq
  rcases h with ⟨m, _, hm⟩ | ⟨i, _, hi⟩
  · rw [← hm]
    exact two_dvd_T r q m
  · rw [← hi]
    exact two_dvd_P r q _ i

lemma sum_S : ∑ s ∈ S r q, s = (q ^ r + B r ^ r) ^ r := by
  have hS := Sk_dvd r (r / 2 - 2) (by omega) (by omega)
  have h3 : 3 ∈ (Finset.range (r + 1)).filter Odd :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨1, rfl⟩⟩
  have hsplit : T r q 3 + ∑ x ∈ Modd r, T r q x
      = ∑ x ∈ (Finset.range (r + 1)).filter Odd, T r q x := Finset.add_sum_erase _ _ h3
  unfold S
  rw [Finset.sum_insert (notMem r q hr hq hBq), Finset.sum_union (disj r q hr hq hBq),
    Finset.sum_image (f := fun s => s) (T_inj r q hr hq hBq),
    Finset.sum_image (f := fun s => s) (P_inj r q hr hq),
    sum_P r q _ (by omega) hS, add_comm (∑ x ∈ Modd r, T r q x) (T r q 3), hsplit,
    sum_eq r q (pow_lt r q (by omega) hBq).le]

lemma card_S : (S r q).card = r - 2 := by
  have h3 : 3 ∈ (Finset.range (r + 1)).filter Odd :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨1, rfl⟩⟩
  have hc : (Modd r).card = (r + 1) / 2 - 1 := by
    unfold Modd
    rw [Finset.card_erase_of_mem h3, card_odd]
  unfold S
  rw [Finset.card_insert_of_notMem (notMem r q hr hq hBq),
    Finset.card_union_of_disjoint (disj r q hr hq hBq),
    Finset.card_image_of_injOn (T_inj r q hr hq hBq),
    Finset.card_image_of_injOn (P_inj r q hr hq), Finset.card_range, hc]
  omega

end

end Q

/-- restated from FormalConjecturesForMathlib/Data/Nat/Prime/Finset.lean -/
@[reducible] def _root_.Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ r.Full s}

namespace Q

lemma mem (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hBq : B r < q) : S r q ∈ Erdos939Sums r := by
  have hqB : ¬ q ∣ B r := not_dvd_small q _ (B_pos r) hBq
  have hS := Sk_dvd r (r / 2 - 2) (by omega) (by omega)
  refine ⟨card_S r q hr hq hBq, ?_, ?_, ?_⟩
  · show (S r q).gcd id = 1
    have h1m : 1 ∈ Modd r := by
      simp only [Modd, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, odd_one⟩
    have h1 : (S r q).gcd id ∣ (q ^ r - B r ^ r) ^ r := Finset.gcd_dvd (Finset.mem_insert_self _ _)
    have h2 : (S r q).gcd id ∣ T r q 1 := Finset.gcd_dvd (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1m)))
    have := Nat.dvd_gcd h1 h2
    rw [(cop r q (by omega) hq hqB (pow_lt r q (by omega) hBq)).gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  · rw [sum_S r q hr hq hBq]
    exact full_pow _ _
  · intro s hs
    unfold S at hs
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hs
    rcases hs with rfl | ⟨m, hm, rfl⟩ | ⟨i, hi, rfl⟩
    · refine ⟨Nat.pos_of_ne_zero (fun h => s0_odd r q (by omega) hq hBq ?_), full_pow _ _⟩
      rw [h]
      exact dvd_zero 2
    · have hm' := mem_Modd r m hm
      have hm1 : 1 ≤ m := by
        obtain ⟨j, hj⟩ := hm'.2.2
        omega
      exact ⟨T_pos r q m hm'.2.1 hq.pos, full_T r q m (by omega) hm1 hm'.2.1⟩
    · refine ⟨?_, full_P r q _ i (by omega) (Finset.mem_range.mp hi) (by omega) hS⟩
      rw [P_mul]
      exact Nat.mul_pos (by omega) (P0_pos r q _ (by omega) hS (Sk_pos _ (by omega)) hq.pos)

end Q

theorem erdos_939.variants.infinite_of_six_le : ∀ r ≥ 6, (Erdos939Sums r).Infinite := by
  intro r hr
  apply Set.Infinite.of_image (fun S : Finset ℕ => ∑ s ∈ S, s)
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (a + Q.B r + 1)
  have hBq : Q.B r < q := by omega
  refine ⟨_, ⟨Q.S r q, Q.mem r q hr hq hBq, rfl⟩, ?_⟩
  show a < ∑ s ∈ Q.S r q, s
  rw [Q.sum_S r q hr hq hBq]
  have h1 : q ≤ q ^ r := Nat.le_self_pow (by omega) q
  have h2 : q ^ r + Q.B r ^ r ≤ (q ^ r + Q.B r ^ r) ^ r := Nat.le_self_pow (by omega) _
  omega

theorem erdos_939.variants.finite : ¬ ∀ r ≥ 4, (Erdos939Sums r).Finite := by
  intro h
  exact erdos_939.variants.infinite_of_six_le 6 le_rfl (h 6 (by omega))

end Erdos939

#print axioms Erdos939.erdos_939.variants.infinite_of_six_le
#print axioms Erdos939.erdos_939.variants.finite
