import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset Filter Nat

namespace G43

/-- Small primes part of the central binomial coefficient (copied from Mathlib's Bertrand). -/
lemma small_part (n : ℕ) (n_pos : 0 < n) :
    ∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ (centralBinom n).factorization x
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n2_pos : 1 ≤ 2 * n := by omega
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  change ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤ _
  rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (by omega)
    have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- Central binomial bound in terms of the number of primes in `(n, 2n]`. -/
lemma cb_le (n : ℕ) (hn : 2 < n) :
    centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ #{p ∈ Finset.Ioc n (2 * n) | p.Prime} := by
  rw [← n.prod_pow_factorization_centralBinom,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.range (2 * n + 1)) (· ≤ 2 * n / 3)]
  have e1 : {x ∈ Finset.range (2 * n + 1) | x ≤ 2 * n / 3} = Finset.range (2 * n / 3 + 1) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [e1]
  apply mul_le_mul' (small_part n (by omega))
  calc ∏ x ∈ Finset.range (2 * n + 1) with ¬ x ≤ 2 * n / 3, x ^ (centralBinom n).factorization x
      ≤ ∏ x ∈ Finset.range (2 * n + 1) with ¬ x ≤ 2 * n / 3,
          (if x.Prime ∧ n < x then 2 * n else 1) := by
        apply Finset.prod_le_prod'
        intro x hx
        rw [Finset.mem_filter, Finset.mem_range] at hx
        split_ifs with h
        · exact pow_factorization_choose_le (by omega)
        · by_cases hp : x.Prime
          · have hxn : x ≤ n := by
              by_contra h'
              exact h ⟨hp, by omega⟩
            rw [factorization_centralBinom_of_two_mul_self_lt_three_mul hn hxn (by omega),
              pow_zero]
          · rw [factorization_eq_zero_of_not_prime _ hp, pow_zero]
    _ = (2 * n) ^ #{x ∈ {x ∈ Finset.range (2 * n + 1) | ¬ x ≤ 2 * n / 3} | x.Prime ∧ n < x} := by
        rw [← Finset.prod_filter, Finset.prod_const]
    _ ≤ _ := by
        apply Nat.pow_le_pow_right (by omega)
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hx ⊢
        exact ⟨⟨hx.2.2, by omega⟩, hx.2.1⟩

/-- Logarithmic form: many primes in `(n, 2n]`. -/
lemma prime_count (n : ℕ) (hn : 2 < n) :
    ((n / 3 : ℕ) : ℝ) * Real.log 4 ≤
      ((1 + Nat.sqrt (2 * n) + #{p ∈ Finset.Ioc n (2 * n) | p.Prime} : ℕ) : ℝ) *
        Real.log (2 * n) := by
  set K := #{p ∈ Finset.Ioc n (2 * n) | p.Prime}
  have h1 := four_pow_le_two_mul_self_mul_centralBinom n (by omega)
  have h2 := cb_le n hn
  have h3 : 4 ^ n ≤ (2 * n) ^ (1 + Nat.sqrt (2 * n) + K) * 4 ^ (2 * n / 3) := by
    calc 4 ^ n ≤ 2 * n * centralBinom n := h1
      _ ≤ 2 * n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ K) := by gcongr
      _ = _ := by ring
  have h4 : 4 ^ (n / 3) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 4 ^ (n / 3) ≤ (2 * n) ^ (1 + Nat.sqrt (2 * n) + K) :=
    le_of_mul_le_mul_right (h4.trans h3) (by positivity)
  have h6 : (((4 : ℕ) ^ (n / 3) : ℕ) : ℝ) ≤ (((2 * n) ^ (1 + Nat.sqrt (2 * n) + K) : ℕ) : ℝ) := by
    exact_mod_cast h5
  push_cast at h6
  have h7 := Real.log_le_log (by positivity) h6
  rw [Real.log_pow, Real.log_pow] at h7
  push_cast at h7 ⊢
  linarith

/-- Residue classes in `[1, N]`. -/
lemma cnt (N m : ℕ) (hm : 0 < m) (v : ℤ) :
    (N : ℝ) / m - 1 ≤ (#{x ∈ Finset.Icc (1 : ℤ) N | x ≡ v [ZMOD m]} : ℝ) ∧
    (#{x ∈ Finset.Icc (1 : ℤ) N | x ≡ v [ZMOD m]} : ℝ) ≤ (N : ℝ) / m + 1 := by
  have hI : Finset.Icc (1 : ℤ) N = Finset.Ioc (0 : ℤ) N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI]
  have h := Int.Ioc_filter_modEq_card 0 (N : ℤ) (r := (m : ℤ)) (by exact_mod_cast hm) v
  set c := #{x ∈ Finset.Ioc (0 : ℤ) N | x ≡ v [ZMOD m]}
  set A : ℚ := (((N : ℤ) : ℚ) - (v : ℚ)) / ((m : ℤ) : ℚ) with hA
  set B : ℚ := (((0 : ℤ) : ℚ) - (v : ℚ)) / ((m : ℤ) : ℚ) with hB
  have hc : (c : ℤ) = max (⌊A⌋ - ⌊B⌋) 0 := h
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have f1 := Int.floor_le A
  have f2 := Int.lt_floor_add_one A
  have f3 := Int.floor_le B
  have f4 := Int.lt_floor_add_one B
  have key : A - B = (N : ℚ) / m := by
    rw [hA, hB]; push_cast; field_simp; ring
  have lo : (N : ℚ) / m - 1 ≤ (c : ℚ) := by
    have h' : (⌊A⌋ - ⌊B⌋ : ℤ) ≤ (c : ℤ) := hc ▸ le_max_left _ _
    have : ((⌊A⌋ - ⌊B⌋ : ℤ) : ℚ) ≤ ((c : ℤ) : ℚ) := by exact_mod_cast h'
    push_cast at this
    linarith
  have hi : (c : ℚ) ≤ (N : ℚ) / m + 1 := by
    rcases le_total (⌊A⌋ - ⌊B⌋) 0 with h0 | h0
    · have : (c : ℤ) = 0 := by rw [hc]; exact max_eq_right h0
      have : (c : ℚ) = 0 := by exact_mod_cast this
      rw [this]; positivity
    · have : (c : ℤ) = ⌊A⌋ - ⌊B⌋ := by rw [hc]; exact max_eq_left h0
      have : (c : ℚ) = ((⌊A⌋ - ⌊B⌋ : ℤ) : ℚ) := by exact_mod_cast this
      rw [this]; push_cast; linarith
  have lo' := (Rat.cast_le (K := ℝ)).2 lo
  have hi' := (Rat.cast_le (K := ℝ)).2 hi
  push_cast at lo' hi'
  exact ⟨lo', hi'⟩

lemma Ap_eq (N p : ℕ) (a : ℤ) :
    {x ∈ Finset.Icc (1 : ℤ) N | (p : ℤ) ∣ x - a} =
      {x ∈ Finset.Icc (1 : ℤ) N | x ≡ a [ZMOD p]} := by
  apply Finset.filter_congr
  intro x _
  rw [Int.modEq_iff_dvd, dvd_sub_comm]

/-- Two classes for distinct primes meet in at most `N/(pq) + 1` points. -/
lemma inter_le (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℤ) :
    (#{x ∈ Finset.Icc (1 : ℤ) N | (p : ℤ) ∣ x - a ∧ (q : ℤ) ∣ x - b} : ℝ) ≤
      (N : ℝ) / (p * q) + 1 := by
  set T := {x ∈ Finset.Icc (1 : ℤ) N | (p : ℤ) ∣ x - a ∧ (q : ℤ) ∣ x - b}
  rcases T.eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · rw [h, Finset.card_empty]; push_cast; positivity
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have hsub : T ⊆ {x ∈ Finset.Icc (1 : ℤ) N | x ≡ x0 [ZMOD ((p * q : ℕ) : ℤ)]} := by
    intro x hx
    simp only [T, Finset.mem_filter] at hx hx0 ⊢
    refine ⟨hx.1, ?_⟩
    have h1 : (p : ℤ) ∣ x - x0 := by
      have := dvd_sub hx.2.1 hx0.2.1; simpa using this
    have h2 : (q : ℤ) ∣ x - x0 := by
      have := dvd_sub hx.2.2 hx0.2.2; simpa using this
    have h3 : ((p * q : ℕ) : ℤ) ∣ x - x0 := by push_cast; exact hcop.mul_dvd h1 h2
    exact (Int.modEq_iff_dvd.2 h3).symm
  have := (cnt N (p * q) (Nat.mul_pos hp.pos hq.pos) x0).2
  calc (#T : ℝ) ≤ #{x ∈ Finset.Icc (1 : ℤ) N | x ≡ x0 [ZMOD ((p * q : ℕ) : ℤ)]} := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by push_cast at this ⊢; exact this

end G43

namespace Green43

open Classical in
noncomputable def sievedSet (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) (N : ℤ)).filter fun n => ∃ p, Nat.Prime p ∧
  lo ≤ (p : ℝ) ∧ (p : ℝ) < hi ∧ (p : ℤ) ∣ ((n : ℤ) - a p)

noncomputable def sievedCard (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : ℕ :=
  (sievedSet N a lo hi).card

def SievedLowerBound (lo hi : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ, (N : ℝ) ^ (1 - ε) ≤ sievedCard N a (lo N) (hi N)

def SievedLowerBoundExp (α : ℝ) : Prop :=
  SievedLowerBound (fun N => (N : ℝ) ^ α) (fun N => 2 * (N : ℝ) ^ α)

/-- Combinatorial core: `k` sieving primes in `[X, 2X)` sieve out `≥ kN/(80X)` integers. -/
lemma core (N : ℕ) (a : ℕ → ℤ) (X : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ X ≤ p ∧ (p : ℝ) < 2 * X) (hX : 12 ≤ X) (hXN : 3 * X ^ 2 ≤ N)
    (hk : (#P : ℝ) ≤ 3 * X) :
    (#P : ℝ) * N / (80 * X) ≤ sievedCard N a X (2 * X) := by
  classical
  set U := Finset.Icc (1 : ℤ) N
  set S := sievedSet N a X (2 * X)
  set k : ℝ := ((#P : ℕ) : ℝ) with hkdef
  let ind : ℕ → ℤ → ℝ := fun p x => if (p : ℤ) ∣ x - a p then 1 else 0
  let c : ℤ → ℝ := fun x => ∑ p ∈ P, ind p x
  have hX0 : 0 < X := by linarith
  have hN0 : (0 : ℝ) < N := by nlinarith
  have hSU : S ⊆ U := Finset.filter_subset _ _
  have hc0 : ∀ x ∈ U, x ∉ S → c x = 0 := by
    intro x hxU hxS
    apply Finset.sum_eq_zero
    intro p hp
    simp only [ind]
    split_ifs with h
    · exact absurd (Finset.mem_filter.2 ⟨hxU, p, (hP p hp).1, (hP p hp).2.1, (hP p hp).2.2, h⟩) hxS
    · rfl
  have hsum1 : ∑ x ∈ U, c x = ∑ x ∈ S, c x := (Finset.sum_subset hSU hc0).symm
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := c)
  have hsq : ∑ x ∈ S, c x ^ 2 ≤ ∑ x ∈ U, c x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hSU (fun _ _ _ => sq_nonneg _)
  have hL : k * (N / (2 * X) - 1) ≤ ∑ x ∈ U, c x := by
    simp only [c]
    rw [Finset.sum_comm]
    have : ∀ p ∈ P, (N : ℝ) / (2 * X) - 1 ≤ ∑ x ∈ U, ind p x := by
      intro p hp
      have hp0 : (0 : ℝ) < p := by linarith [(hP p hp).2.1]
      simp only [ind]
      rw [Finset.sum_boole, G43.Ap_eq]
      have := (G43.cnt N p (hP p hp).1.pos (a p)).1
      have h2 : (N : ℝ) / (2 * X) ≤ N / p :=
        div_le_div_of_nonneg_left hN0.le hp0 (hP p hp).2.2.le
      linarith
    calc k * (N / (2 * X) - 1) = ∑ p ∈ P, ((N : ℝ) / (2 * X) - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum this
  have hQ : ∑ x ∈ U, c x ^ 2 ≤ k * (k * (N / X ^ 2 + 1) + N / X) := by
    have expand : ∀ x, c x ^ 2 = ∑ p ∈ P, ∑ q ∈ P, ind p x * ind q x := by
      intro x; simp only [c]; rw [sq, Finset.sum_mul_sum]
    simp_rw [expand]
    have hpq : ∀ p ∈ P, ∀ q ∈ P, ∑ x ∈ U, ind p x * ind q x ≤
        N / X ^ 2 + 1 + (if p = q then (N : ℝ) / X else 0) := by
      intro p hp q hq
      have hp0 : X ≤ (p : ℝ) := (hP p hp).2.1
      have hq0 : X ≤ (q : ℝ) := (hP q hq).2.1
      have e : ∀ x, ind p x * ind q x =
          if ((p : ℤ) ∣ x - a p ∧ (q : ℤ) ∣ x - a q) then 1 else 0 := by
        intro x; simp only [ind]; split_ifs <;> simp_all
      simp_rw [e]
      rw [Finset.sum_boole]
      by_cases h : p = q
      · subst h
        simp only [and_self, if_true]
        rw [G43.Ap_eq]
        have := (G43.cnt N p (hP p hp).1.pos (a p)).2
        have h2 : (N : ℝ) / p ≤ N / X := div_le_div_of_nonneg_left hN0.le hX0 hp0
        have h3 : (0 : ℝ) ≤ N / X ^ 2 := by positivity
        linarith
      · rw [if_neg h]
        have := G43.inter_le N p q (hP p hp).1 (hP q hq).1 h (a p) (a q)
        have h2 : (N : ℝ) / (p * q) ≤ N / X ^ 2 := by
          apply div_le_div_of_nonneg_left hN0.le (by positivity)
          rw [sq]; exact mul_le_mul hp0 hq0 hX0.le (by linarith)
        linarith
    calc ∑ x ∈ U, ∑ p ∈ P, ∑ q ∈ P, ind p x * ind q x
        = ∑ p ∈ P, ∑ q ∈ P, ∑ x ∈ U, ind p x * ind q x := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
      _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((N : ℝ) / X ^ 2 + 1 + (if p = q then (N : ℝ) / X else 0)) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hpq p hp q hq
      _ = ∑ p ∈ P, (k * (N / X ^ 2 + 1) + N / X) := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq, if_pos hp,
            nsmul_eq_mul]
      _ = k * (k * (N / X ^ 2 + 1) + N / X) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- final arithmetic
  set L := ∑ x ∈ U, c x
  set Q := ∑ x ∈ U, c x ^ 2
  set s : ℝ := ((#S : ℕ) : ℝ)
  set Y : ℝ := N / X with hYdef
  have hNY : (N : ℝ) = Y * X := by rw [hYdef]; field_simp
  have hY3 : 3 * X ≤ Y := by
    rw [hYdef, le_div_iff₀ hX0]; nlinarith
  have hY0 : 0 < Y := by linarith
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have e1 : (N : ℝ) / (2 * X) = Y / 2 := by rw [hNY]; field_simp
  have e2 : (N : ℝ) / X ^ 2 = Y / X := by rw [hNY]; field_simp
  rw [e1] at hL
  rw [e2] at hQ
  have hL2 : k * Y / 4 ≤ L := by nlinarith
  have hQ2 : Q ≤ 5 * k * Y := by
    have : k * (Y / X + 1) ≤ 3 * X * (Y / X + 1) := by
      apply mul_le_mul_of_nonneg_right hk; positivity
    have h4 : 3 * X * (Y / X + 1) = 3 * Y + 3 * X := by field_simp
    nlinarith
  have hS : L ^ 2 ≤ s * Q := by
    rw [hsum1]; exact hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  have h5 : (k * Y / 4) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (div_nonneg (mul_nonneg hk0 hY0.le) (by norm_num)) hL2 2
  have h6 : s * Q ≤ s * (5 * k * Y) := mul_le_mul_of_nonneg_left hQ2 (Nat.cast_nonneg _)
  show k * N / (80 * X) ≤ s
  have goal_eq : k * N / (80 * X) = k * Y / 80 := by rw [hNY]; field_simp
  rw [goal_eq]
  rcases hk0.eq_or_lt with hk' | hk'
  · rw [← hk', zero_mul, zero_div]; exact Nat.cast_nonneg _
  · have hkY : 0 < k * Y := mul_pos hk' hY0
    have : k * Y * (k * Y / 80) ≤ k * Y * s := by nlinarith
    exact le_of_mul_le_mul_left this hkY

lemma ev_pow {γ : ℝ} (hγ : 0 < γ) (C : ℝ) : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ γ :=
  ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

lemma arith (η X t w k s K : ℝ) (ht0 : 0 < t) (hw0 : 0 < w) (hX12 : 12 ≤ X)
    (hXwt : X = (w * t) ^ 2) (hηt : 5120 ≤ η * t) (hηw : 320 ≤ η * w)
    (hK1 : η * X ≤ 32 * t * (1 + s + K)) (hs : s ≤ 2 * (w * t)) (hKP : K ≤ k + 2) :
    80 * X ≤ k * (t * t) := by
  have hwt0 : 0 < w * t := mul_pos hw0 ht0
  have hwt1 : 1 ≤ w * t := by nlinarith
  have h1 : η * w ^ 2 * t ≤ 32 * (1 + s + K) := by
    have e : η * X = t * (η * w ^ 2 * t) := by rw [hXwt]; ring
    rw [e] at hK1
    have : t * (η * w ^ 2 * t) ≤ t * (32 * (1 + s + K)) := by linarith
    exact le_of_mul_le_mul_left this ht0
  have k1 : w ^ 2 * 5120 ≤ w ^ 2 * (η * t) := mul_le_mul_of_nonneg_left hηt (sq_nonneg w)
  have k2 : 320 * (w * t) ≤ η * w * (w * t) := mul_le_mul_of_nonneg_right hηw hwt0.le
  have hk : 80 * w ^ 2 ≤ k := by
    have e1 : w ^ 2 * (η * t) = η * w ^ 2 * t := by ring
    have e2 : η * w * (w * t) = η * w ^ 2 * t := by ring
    rw [e1] at k1
    rw [e2] at k2
    linarith
  calc 80 * X = (80 * w ^ 2) * (t * t) := by rw [hXwt]; ring
    _ ≤ k * (t * t) := mul_le_mul_of_nonneg_right hk (by positivity)

lemma main_bound (N : ℕ) (a : ℕ → ℤ) (η X t w : ℝ) (hN0 : (0 : ℝ) < N) (hη0 : 0 < η)
    (hX12 : 12 ≤ X) (hX2 : 3 * X ^ 2 ≤ N) (hXwt : X = (w * t) ^ 2) (ht0 : 0 < t) (hw0 : 0 < w)
    (hηt : 5120 ≤ η * t) (hηw : 320 ≤ η * w)
    (hlog : ∀ n : ℕ, (n : ℝ) < X + 1 → η * Real.log (2 * n) ≤ 4 * t) :
    (N : ℝ) / (t * t) ≤ sievedCard N a X (2 * X) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨n, hndef⟩ : ∃ n, n = ⌈X⌉₊ := ⟨_, rfl⟩
  have hn1 : X ≤ n := hndef ▸ Nat.le_ceil X
  have hn2 : (n : ℝ) < X + 1 := hndef ▸ Nat.ceil_lt_add_one hX0.le
  have hn3 : 2 < n := by
    have : (2 : ℝ) < n := by linarith
    exact_mod_cast this
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = {p ∈ Finset.Ioc n (2 * n - 2) | p.Prime} :=
    ⟨_, rfl⟩
  have hP : ∀ p ∈ P, p.Prime ∧ X ≤ p ∧ (p : ℝ) < 2 * X := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have h1 : n + 1 ≤ p := hp.1.1
    have h2 : p + 2 ≤ 2 * n := by omega
    have h1' : (n : ℝ) + 1 ≤ p := by exact_mod_cast h1
    have h2' : (p : ℝ) + 2 ≤ 2 * n := by exact_mod_cast h2
    exact ⟨hp.2, by linarith, by linarith⟩
  have hk : (#P : ℝ) ≤ 3 * X := by
    have : #P ≤ n := by
      calc #P ≤ #(Finset.Ioc n (2 * n - 2)) := by rw [hPdef]; exact Finset.card_filter_le _ _
        _ = 2 * n - 2 - n := Nat.card_Ioc _ _
        _ ≤ n := by omega
    have : (#P : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hcore := core N a X P hP hX12 hX2 hk
  obtain ⟨K, hKdef⟩ : ∃ K, K = #{p ∈ Finset.Ioc n (2 * n) | p.Prime} := ⟨_, rfl⟩
  have hKP : K ≤ #P + 2 := by
    have hsub : {p ∈ Finset.Ioc n (2 * n) | p.Prime} ⊆ P ∪ {2 * n - 1, 2 * n} := by
      intro p hp
      rw [hPdef]
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hp ⊢
      by_cases h : p ≤ 2 * n - 2
      · left; exact ⟨⟨hp.1.1, h⟩, hp.2⟩
      · right; omega
    rw [hKdef]
    calc #{p ∈ Finset.Ioc n (2 * n) | p.Prime} ≤ #(P ∪ {2 * n - 1, 2 * n}) :=
          Finset.card_le_card hsub
      _ ≤ #P + #({2 * n - 1, 2 * n} : Finset ℕ) := Finset.card_union_le _ _
      _ ≤ #P + 2 := by gcongr; exact Finset.card_le_two
  have hpc := G43.prime_count n hn3
  rw [← hKdef] at hpc
  obtain ⟨s, hsdef⟩ : ∃ s, s = Nat.sqrt (2 * n) := ⟨_, rfl⟩
  rw [← hsdef] at hpc
  push_cast at hpc
  have hlog4 : (3 / 4 : ℝ) ≤ Real.log 4 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
    have e : (1 : ℝ) - 4⁻¹ = 3 / 4 := by norm_num
    linarith
  have hm : X / 4 ≤ ((n / 3 : ℕ) : ℝ) := by
    have h : n ≤ 3 * (n / 3) + 2 := by omega
    have h' : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast h
    linarith
  have hlogn := hlog n hn2
  have hs : (s : ℝ) ≤ 2 * (w * t) := by
    have h1 : (s : ℝ) ≤ Real.sqrt ((2 * n : ℕ) : ℝ) := hsdef ▸ Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt ((2 * n : ℕ) : ℝ) ≤ Real.sqrt (4 * X) := by
      apply Real.sqrt_le_sqrt; push_cast; linarith
    have h3 : Real.sqrt (4 * X) = 2 * (w * t) := by
      rw [hXwt, show (4 : ℝ) * (w * t) ^ 2 = (2 * (w * t)) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    linarith
  have hK1 : η * X ≤ 32 * t * (1 + s + K) := by
    have h1 : X / 4 * (3 / 4) ≤ ((n / 3 : ℕ) : ℝ) * Real.log 4 :=
      mul_le_mul hm hlog4 (by norm_num) (by positivity)
    have h3 : 3 * X / 16 ≤ (1 + (s : ℝ) + K) * Real.log (2 * n) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hη0.le
    have h5 := mul_le_mul_of_nonneg_left hlogn (by positivity : (0 : ℝ) ≤ 1 + s + K)
    have h6 : 0 ≤ (1 + (s : ℝ) + K) * t := by positivity
    linarith
  have hKP' : (K : ℝ) ≤ #P + 2 := by exact_mod_cast hKP
  have hkk := arith η X t w (#P) s K ht0 hw0 hX12 hXwt hηt hηw hK1 hs hKP'
  calc (N : ℝ) / (t * t) ≤ (#P : ℝ) * N / (80 * X) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hkk hN0.le]
    _ ≤ _ := hcore

theorem green_43.variants.general_exponent_lt_half :
    ∀ α : ℝ, 0 < α → α < 1 / 2 → SievedLowerBoundExp α := by
  intro α hα hα2 ε hε
  obtain ⟨δ, hδ0, hδε, hδα⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * δ ≤ ε ∧ δ ≤ α / 4 :=
    ⟨min (ε / 2) (α / 4), lt_min (by linarith) (by linarith),
      by have := min_le_left (ε / 2) (α / 4); linarith, min_le_right _ _⟩
  obtain ⟨η, hη⟩ : ∃ η, η = δ / α := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ div_pos hδ0 hα
  have hη1 : η ≤ 1 := by rw [hη, div_le_one hα]; linarith
  filter_upwards [ev_pow hα 12, ev_pow (by linarith : (0:ℝ) < 1 - 2 * α) 3,
    ev_pow hδ0 (5120 / η), ev_pow (by linarith : (0:ℝ) < α / 2 - δ) (320 / η),
    eventually_ge_atTop 1] with N hX12 hN3 ht hw hN1 a
  show (N : ℝ) ^ (1 - ε) ≤ sievedCard N a ((N : ℝ) ^ α) (2 * (N : ℝ) ^ α)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNe : (N : ℝ) ^ (1 - ε) ≤ N / ((N : ℝ) ^ δ * (N : ℝ) ^ δ) := by
    have h1 : (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 - 2 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h2 : (N : ℝ) ^ (1 - 2 * δ) = N / ((N : ℝ) ^ δ * (N : ℝ) ^ δ) := by
      rw [show 1 - 2 * δ = 1 - (δ + δ) by ring, Real.rpow_sub hN0, Real.rpow_one,
        Real.rpow_add hN0]
    linarith
  have hsq : Real.sqrt ((N : ℝ) ^ α) = (N : ℝ) ^ (α / 2 - δ) * (N : ℝ) ^ δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; ring
  have hX2 : 3 * ((N : ℝ) ^ α) ^ 2 ≤ N := by
    have e : ((N : ℝ) ^ α) ^ 2 = (N : ℝ) ^ (2 * α) := by
      rw [← Real.rpow_mul_natCast hN0.le]; congr 1; push_cast; ring
    have hsplit : (N : ℝ) = (N : ℝ) ^ (2 * α) * (N : ℝ) ^ (1 - 2 * α) := by
      rw [← Real.rpow_add hN0, show 2 * α + (1 - 2 * α) = 1 by ring, Real.rpow_one]
    rw [e]
    calc 3 * (N : ℝ) ^ (2 * α) ≤ (N : ℝ) ^ (2 * α) * (N : ℝ) ^ (1 - 2 * α) := by
          nlinarith [Real.rpow_nonneg hN0.le (2 * α)]
      _ = N := hsplit.symm
  have hX4 : ((4 : ℝ) * (N : ℝ) ^ α) ^ η = (4 : ℝ) ^ η * (N : ℝ) ^ δ := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le]
    congr 2; rw [hη]; field_simp
  have ht0 : 0 < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hN0 _
  have hw0 : 0 < (N : ℝ) ^ (α / 2 - δ) := Real.rpow_pos_of_pos hN0 _
  have hX0 : 0 < (N : ℝ) ^ α := by linarith
  have hXwt : (N : ℝ) ^ α = ((N : ℝ) ^ (α / 2 - δ) * (N : ℝ) ^ δ) ^ 2 := by
    rw [← hsq, Real.sq_sqrt hX0.le]
  have hηt : 5120 ≤ η * (N : ℝ) ^ δ := by
    rw [div_le_iff₀ hη0] at ht; linarith
  have hηw : 320 ≤ η * (N : ℝ) ^ (α / 2 - δ) := by
    rw [div_le_iff₀ hη0] at hw; linarith
  have hlog : ∀ n : ℕ, (n : ℝ) < (N : ℝ) ^ α + 1 →
      η * Real.log (2 * n) ≤ 4 * (N : ℝ) ^ δ := by
    intro n hn2
    have h1 := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ 2 * n) hη0
    have h2 : ((2 : ℝ) * n) ^ η ≤ (4 * (N : ℝ) ^ α) ^ η :=
      Real.rpow_le_rpow (by positivity) (by linarith) hη0.le
    have h4 : (4 : ℝ) ^ η ≤ 4 := by
      calc (4 : ℝ) ^ η ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
        _ = 4 := Real.rpow_one 4
    have h5 : ((2 : ℝ) * n) ^ η ≤ 4 * (N : ℝ) ^ δ := by
      calc _ ≤ (4 * (N : ℝ) ^ α) ^ η := h2
        _ = 4 ^ η * (N : ℝ) ^ δ := hX4
        _ ≤ 4 * (N : ℝ) ^ δ := by gcongr
    calc η * Real.log (2 * n) ≤ η * (((2 : ℝ) * n) ^ η / η) :=
          mul_le_mul_of_nonneg_left h1 hη0.le
      _ = ((2 : ℝ) * n) ^ η := by field_simp
      _ ≤ _ := h5
  have hmain := main_bound N a η ((N : ℝ) ^ α) ((N : ℝ) ^ δ) ((N : ℝ) ^ (α / 2 - δ)) hN0 hη0
    hX12 hX2 hXwt ht0 hw0 hηt hηw hlog
  exact hNe.trans hmain

end Green43

#print axioms Green43.green_43.variants.general_exponent_lt_half
