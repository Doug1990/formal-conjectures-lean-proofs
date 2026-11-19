import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Lattice.Nat

open Filter

namespace Erdos294

def HasUnitFractionSolution (m N : ℕ) : Prop :=
  ∃ s : Finset ℕ, m ∈ s ∧ (∀ n ∈ s, m ≤ n ∧ n ≤ N) ∧ ∑ n ∈ s, (1 : ℚ) / n = 1

noncomputable def t (N : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ¬ HasUnitFractionSolution m N}

namespace U

lemma termB (p Q R n : ℕ) (hn : n ≠ 0) (h : n ∣ Q) :
    ((p * Q * R : ℕ) : ℚ) * (1 / n) = ((p * R * (Q / n) : ℕ) : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hn)]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

lemma termA (p Q R n d : ℕ) (hn : n = p * d) (hd : d ≠ 0) (hp : p ≠ 0) (h : d ∣ R) :
    ((p * Q * R : ℕ) : ℚ) * (1 / n) = ((Q * (R / d) : ℕ) : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  subst hn
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd)]
  have : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  push_cast
  field_simp

lemma no_sol (p k N : ℕ) (hp : p.Prime) (hk : k * Nat.lcmUpto k < p) (hN : N < p * (k + 1)) :
    ¬ HasUnitFractionSolution p N := by
  rintro ⟨s, hps, hall, hs⟩
  classical
  set R := Nat.lcmUpto k with hR
  set A := s.filter (fun n => p ∣ n) with hA
  set B := s.filter (fun n => ¬ p ∣ n) with hB
  set Q := ∏ n ∈ B, n with hQ
  have hp0 : p ≠ 0 := hp.ne_zero
  -- facts on A
  have hAd : ∀ n ∈ A, n = p * (n / p) ∧ 1 ≤ n / p ∧ n / p ≤ k := by
    intro n hn
    rw [hA, Finset.mem_filter] at hn
    obtain ⟨hns, hpn⟩ := hn
    have h1 : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    refine ⟨h1, ?_, ?_⟩
    · have := (hall n hns).1
      rcases Nat.eq_zero_or_pos (n / p) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact h
    · have h2 := (hall n hns).2
      by_contra hc
      push Not at hc
      have : p * (k + 1) ≤ p * (n / p) := Nat.mul_le_mul_left p hc
      omega
  have hAdvd : ∀ n ∈ A, n / p ∣ R := by
    intro n hn
    obtain ⟨-, h1, h2⟩ := hAd n hn
    exact Finset.dvd_lcm (s := Finset.Icc 1 k) (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hBne : ∀ n ∈ B, n ≠ 0 := by
    intro n hn
    rw [hB, Finset.mem_filter] at hn
    have := (hall n hn.1).1
    have := hp.pos
    omega
  have hBdvd : ∀ n ∈ B, n ∣ Q := fun n hn => Finset.dvd_prod_of_mem _ hn
  -- rational identity
  have hq : ((p * Q * R : ℕ) : ℚ) =
      ∑ n ∈ A, ((Q * (R / (n / p)) : ℕ) : ℚ) + ∑ n ∈ B, ((p * R * (Q / n) : ℕ) : ℚ) := by
    calc ((p * Q * R : ℕ) : ℚ) = ((p * Q * R : ℕ) : ℚ) * ∑ n ∈ s, (1 : ℚ) / n := by
          rw [hs, mul_one]
      _ = ∑ n ∈ s, ((p * Q * R : ℕ) : ℚ) * (1 / n) := Finset.mul_sum _ _ _
      _ = ∑ n ∈ A, ((p * Q * R : ℕ) : ℚ) * (1 / n) + ∑ n ∈ B, ((p * Q * R : ℕ) : ℚ) * (1 / n) :=
          (Finset.sum_filter_add_sum_filter_not s _ _).symm
      _ = _ := by
          congr 1
          · refine Finset.sum_congr rfl (fun n hn => ?_)
            obtain ⟨h1, h2, -⟩ := hAd n hn
            exact termA p Q R n (n / p) h1 (by omega) hp0 (hAdvd n hn)
          · exact Finset.sum_congr rfl (fun n hn => termB p Q R n (hBne n hn) (hBdvd n hn))
  have hnat : p * Q * R = ∑ n ∈ A, Q * (R / (n / p)) + ∑ n ∈ B, p * R * (Q / n) := by
    exact_mod_cast hq
  set X := ∑ n ∈ A, R / (n / p) with hX
  have hnat2 : p * Q * R = Q * X + p * (∑ n ∈ B, R * (Q / n)) := by
    rw [hnat, hX, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => by ring)
  have hdvd : p ∣ Q * X := by
    have h1 : p ∣ p * Q * R := by rw [mul_assoc]; exact dvd_mul_right p _
    rw [hnat2] at h1
    exact (Nat.dvd_add_left (dvd_mul_right p _)).mp h1
  have hQ' : ¬ p ∣ Q := by
    intro h
    rw [hQ] at h
    obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    rw [hB, Finset.mem_filter] at hn
    exact hn.2 hpn
  have hpX : p ∣ X := (Nat.Prime.dvd_mul hp).mp hdvd |>.resolve_left hQ'
  have hpA : p ∈ A := by
    rw [hA, Finset.mem_filter]; exact ⟨hps, dvd_refl p⟩
  have hRpos : 0 < R := Nat.lcmUpto_pos k
  have hXpos : 0 < X := by
    have : R / (p / p) ≤ X := Finset.single_le_sum (f := fun n => R / (n / p))
      (fun _ _ => Nat.zero_le _) hpA
    rw [Nat.div_self hp.pos, Nat.div_one] at this
    omega
  have hcardA : A.card ≤ k := by
    have hsub : A ⊆ (Finset.Icc 1 k).image (fun d => p * d) := by
      intro n hn
      obtain ⟨h1, h2, h3⟩ := hAd n hn
      exact Finset.mem_image.mpr ⟨n / p, Finset.mem_Icc.mpr ⟨h2, h3⟩, h1.symm⟩
    calc A.card ≤ ((Finset.Icc 1 k).image (fun d => p * d)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 k).card := Finset.card_image_le
      _ = k := by simp
  have hXle : X ≤ k * R := by
    calc X ≤ ∑ n ∈ A, R := Finset.sum_le_sum (fun n _ => Nat.div_le_self _ _)
      _ = A.card * R := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ k * R := Nat.mul_le_mul_right R hcardA
  have := Nat.le_of_dvd hXpos hpX
  omega

lemma t_le (p k N : ℕ) (hp : p.Prime) (hk : k * Nat.lcmUpto k < p) (hN : N < p * (k + 1)) :
    t N ≤ p :=
  Nat.sInf_le ⟨hp.pos, no_sol p k N hp hk hN⟩

lemma lcm_le (k : ℕ) : (Nat.lcmUpto k : ℝ) ≤ Real.exp (7 * k) := by
  have h1 := Chebyshev.psi_le_const_mul_self (x := (k : ℝ)) (Nat.cast_nonneg k)
  rw [Chebyshev.psi_eq_log_lcmUpto] at h1
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := 4) (by norm_num)
    linarith
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : Real.log (Nat.lcmUpto k) ≤ 7 * k := by nlinarith
  have hpos : (0:ℝ) < Nat.lcmUpto k := by exact_mod_cast Nat.lcmUpto_pos k
  calc (Nat.lcmUpto k : ℝ) = Real.exp (Real.log (Nat.lcmUpto k)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (7 * k) := Real.exp_le_exp.mpr h2

lemma main_bound (N : ℕ) (hN : 28 ≤ Real.log N) : (t N : ℝ) * Real.log N ≤ 56 * N := by
  set L := Real.log N with hL
  have hNpos : (0:ℝ) < N := by
    by_contra h
    push Not at h
    have : (N:ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    rw [hL, this, Real.log_zero] at hN
    linarith
  set k := ⌊L / 28⌋₊ with hk
  have hk1 : (k:ℝ) ≤ L / 28 := Nat.floor_le (by linarith)
  have hk2 : L / 28 < k + 1 := Nat.lt_floor_add_one _
  set u := Real.exp (L / 4) with hu
  have hu4 : u ^ 4 = N := by
    rw [hu, ← Real.exp_nat_mul]
    push_cast
    rw [show (4:ℝ) * (L / 4) = L by ring, hL, Real.exp_log hNpos]
  have hupos : 0 < u := Real.exp_pos _
  have hLu : L ≤ 4 * u := by
    have := Real.log_le_sub_one_of_pos hupos
    rw [hu, Real.log_exp] at this
    linarith
  have hu7 : 4 ≤ u := by
    have := Real.add_one_le_exp (L / 4)
    rw [← hu] at this
    linarith
  have hlcm : (Nat.lcmUpto k : ℝ) ≤ u := by
    refine (lcm_le k).trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hkr : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hlcm0 : (0:ℝ) ≤ Nat.lcmUpto k := Nat.cast_nonneg _
  -- k (k+1) lcm ≤ N
  have hprod : ((k * Nat.lcmUpto k * (k + 1) : ℕ) : ℝ) ≤ N := by
    push_cast
    have a1 : (k:ℝ) ≤ u := by linarith
    have a2 : (k:ℝ) + 1 ≤ 4 * u := by linarith
    calc (k:ℝ) * Nat.lcmUpto k * (k + 1) ≤ u * u * (4 * u) := by
          apply mul_le_mul (mul_le_mul a1 hlcm hlcm0 hupos.le) a2 (by linarith) (by positivity)
      _ ≤ u ^ 4 := by nlinarith
      _ = N := hu4
  have hprodN : k * Nat.lcmUpto k * (k + 1) ≤ N := by exact_mod_cast hprod
  set M := N / (k + 1) with hM
  have hkM : k * Nat.lcmUpto k ≤ M := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr hprodN
  have hk1N : k + 1 ≤ N := by
    have : ((k:ℝ) + 1) ≤ N := by
      have := Real.log_le_sub_one_of_pos hNpos
      linarith
    exact_mod_cast this
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact (Nat.div_pos hk1N (Nat.succ_pos k)).ne'
  obtain ⟨p, hp, hMp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul M hM0
  have hNlt : N < p * (k + 1) := by
    have h1 := Nat.div_add_mod N (k + 1)
    have h2 := Nat.mod_lt N (Nat.succ_pos k)
    have h3 : (M + 1) * (k + 1) ≤ p * (k + 1) := Nat.mul_le_mul_right _ hMp
    rw [← hM] at h1
    nlinarith
  have ht := t_le p k N hp (by omega) hNlt
  have hMk : (M : ℝ) * (k + 1) ≤ N := by
    have : M * (k + 1) ≤ N := Nat.div_mul_le_self N (k + 1)
    exact_mod_cast this
  have hpr : (p : ℝ) ≤ 2 * M := by exact_mod_cast hp2
  have htr : (t N : ℝ) ≤ p := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t N := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  calc (t N : ℝ) * L ≤ p * L := mul_le_mul_of_nonneg_right htr hL0
    _ ≤ (2 * M) * (28 * (k + 1)) := by
        apply mul_le_mul hpr (by linarith) hL0 (by positivity)
    _ = 56 * (M * (k + 1)) := by ring
    _ ≤ 56 * N := by linarith

end U

theorem erdos_294.variants.erdos_graham_upper :
    Asymptotics.IsBigO atTop (fun N : ℕ => (t N : ℝ)) (fun N : ℕ => (N : ℝ) / Real.log N) := by
  refine Asymptotics.IsBigO.of_bound 56 ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp 28⌉₊, fun N hN => ?_⟩
  have hN' : Real.exp 28 ≤ N := Nat.ceil_le.mp hN
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN'
  have hL : 28 ≤ Real.log N := by
    rw [← Real.log_exp 28]
    exact Real.log_le_log (Real.exp_pos _) hN'
  have hLpos : 0 < Real.log N := by linarith
  have hb := U.main_bound N hL
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hLpos.le), mul_div_assoc', le_div_iff₀ hLpos]
  exact hb

end Erdos294

#print axioms Erdos294.erdos_294.variants.erdos_graham_upper
