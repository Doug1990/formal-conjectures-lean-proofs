import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Real

namespace Erdos945

abbrev τ  := fun (n : ℕ) => n.divisors.card

noncomputable def F (x : ℝ) : ℕ :=
  sSup {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

def Erdos945Prop : Prop := ∃ O : ℝ → ℝ, O =O[atTop] (1 : ℝ → ℝ) ∧ ∀ᶠ x in atTop, F x ≤ log x ^ O x

def Erdos945Constant : Prop :=
  ∃ C > (0 : ℝ),  ∀ᶠ x : ℝ in atTop,
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + log x ^ C) ∧
    ↑b ∈ Set.Icc x (x + log x ^ C) ∧
    τ a = τ b

lemma F_le (x B : ℝ) (hB : 0 ≤ B)
    (h : ∀ n k : ℕ, ((n : ℝ) + k) ≤ x → (Set.Ioc n (n + k)).InjOn τ → (k : ℝ) ≤ B) :
    (F x : ℝ) ≤ B := by
  unfold F
  refine le_trans (Nat.cast_le.2 (csSup_le' ?_)) (Nat.floor_le hB)
  rintro k ⟨n, hn, hinj⟩
  exact Nat.le_floor (h n k (by exact_mod_cast hn) hinj)

lemma le_F (y : ℝ) (n k : ℕ) (hn : (n : ℝ) + k ≤ y) (hinj : (Set.Ioc n (n + k)).InjOn τ) :
    k ≤ F y := by
  unfold F
  apply le_csSup
  · refine ⟨⌊y⌋₊, ?_⟩
    rintro j ⟨m, hm, _⟩
    apply Nat.le_floor
    have hm' : (m : ℝ) + j ≤ y := by exact_mod_cast hm
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · exact ⟨n, by exact_mod_cast hn, hinj⟩

theorem const_to_prop : Erdos945Constant → Erdos945Prop := by
  rintro ⟨C, hC, hev⟩
  rw [eventually_atTop] at hev
  obtain ⟨X0, hX0⟩ := hev
  set N0 : ℕ := ⌈max X0 1⌉₊ with hN0
  refine ⟨fun _ => C + 1, Asymptotics.isBigO_const_const (C + 1) (one_ne_zero (α := ℝ)) atTop, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((N0 : ℝ) + 2),
    eventually_ge_atTop (1 : ℝ)] with x hlx hx1
  have hlog0 : 0 ≤ log x := by linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  apply F_le _ _ (Real.rpow_nonneg hlog0 _)
  intro n k hnk hinj
  by_contra hlt
  push Not at hlt
  set P := log x ^ C with hP
  have hl1 : 1 ≤ log x := by linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
  have hP1 : 1 ≤ P := Real.one_le_rpow hl1 hC.le
  have hsplit : log x ^ (C + 1) = log x * P := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]; ring
  rw [hsplit] at hlt
  have hmul := mul_le_mul_of_nonneg_right hlx (by linarith : (0 : ℝ) ≤ P)
  have hkbig : (N0 : ℝ) + 1 + P < k := by nlinarith
  have hkN : N0 + 1 < k := by
    have : (N0 : ℝ) + 1 < k := by linarith
    exact_mod_cast this
  set m : ℕ := max (n + 1) N0 with hm
  have hmle : m ≤ n + k := by omega
  have hmle2 : m ≤ n + 1 + N0 := by omega
  have hX0m : X0 ≤ (m : ℝ) := by
    have h1 : max X0 1 ≤ (N0 : ℝ) := Nat.le_ceil _
    have h2 : (N0 : ℝ) ≤ m := by exact_mod_cast (le_max_right _ _ : N0 ≤ m)
    linarith [le_max_left X0 1]
  have hm1 : (1 : ℝ) ≤ m := by
    have h1 : max X0 1 ≤ (N0 : ℝ) := Nat.le_ceil _
    have h2 : (N0 : ℝ) ≤ m := by exact_mod_cast (le_max_right _ _ : N0 ≤ m)
    linarith [le_max_right X0 1]
  have hmx : (m : ℝ) ≤ x := by
    have : (m : ℝ) ≤ n + k := by exact_mod_cast hmle
    linarith
  have hlogm : log m ^ C ≤ P :=
    Real.rpow_le_rpow (Real.log_nonneg hm1) (Real.log_le_log (by linarith) hmx) hC.le
  obtain ⟨a, b, hab, ha, hb, hτ⟩ := hX0 m hX0m
  have hm2 : (m : ℝ) ≤ n + 1 + N0 := by exact_mod_cast hmle2
  have hnm : (n : ℝ) < m := by
    have : n < m := by omega
    exact_mod_cast this
  have mem : ∀ c : ℕ, (c : ℝ) ∈ Set.Icc (m : ℝ) (m + log m ^ C) → c ∈ Set.Ioc n (n + k) := by
    intro c hc
    have h1 : (n : ℝ) < c := by linarith [hc.1]
    have h2 : (c : ℝ) ≤ n + k := by linarith [hc.2]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  exact hab (hinj (mem a ha) (mem b hb) hτ)

theorem prop_to_const : Erdos945Prop → Erdos945Constant := by
  rintro ⟨O, hO, hev⟩
  obtain ⟨c, hc⟩ := hO.bound
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  refine ⟨c' + 1, by linarith, ?_⟩
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 (hev.and hc)
  have E2 := (isLittleO_log_rpow_rpow_atTop (c' + 1) one_pos).bound one_pos
  filter_upwards [E2, eventually_ge_atTop (max X1 2),
    Real.tendsto_log_atTop.eventually_ge_atTop ((2 : ℝ) ^ c' + 2)] with x h2 hx hlx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxX : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ c' := Real.rpow_pos_of_pos (by norm_num) _
  set t := log x with ht
  have ht1 : 1 ≤ t := by linarith
  set L := t ^ (c' + 1) with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (by linarith) _
  have hLx : L ≤ x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, Real.rpow_one] at h2
    exact (le_abs_self _).trans (h2.trans (le_of_eq (abs_of_nonneg (by linarith))))
  by_contra hne
  set m0 := ⌈x⌉₊ with hm0
  have hm0pos : 0 < m0 := Nat.ceil_pos.2 (by linarith)
  set n := m0 - 1 with hn
  have hn1 : n + 1 = m0 := by omega
  have hn1r : (n : ℝ) + 1 = m0 := by exact_mod_cast hn1
  have hxm : x ≤ (m0 : ℝ) := Nat.le_ceil x
  have hmx : (m0 : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  set K := ⌊L⌋₊ with hK
  have hKL : (K : ℝ) ≤ L := Nat.floor_le hL0
  have hKL' : L < K + 1 := Nat.lt_floor_add_one L
  set y := x + L with hy
  have hinj : (Set.Ioc n (n + K)).InjOn τ := by
    intro a ha b hb hτ
    by_contra hab
    have mem : ∀ c : ℕ, c ∈ Set.Ioc n (n + K) → (c : ℝ) ∈ Set.Icc x (x + log x ^ (c' + 1)) := by
      intro c hc
      have h1 : n + 1 ≤ c := hc.1
      have h2 : c ≤ n + K := hc.2
      have h1' : (n : ℝ) + 1 ≤ c := by exact_mod_cast h1
      have h2' : (c : ℝ) ≤ n + K := by exact_mod_cast h2
      constructor
      · linarith
      · show (c : ℝ) ≤ x + L
        linarith
    exact hne ⟨a, b, hab, mem a ha, mem b hb, hτ⟩
  have hKF : K ≤ F y := le_F y n K (by linarith) hinj
  obtain ⟨hFy, hOy⟩ := hX1 y (by linarith)
  rw [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs] at hOy
  have hOc : O y ≤ c' := le_trans (le_abs_self _) (hOy.trans (le_max_left _ _))
  have hyx2 : y ≤ x ^ 2 := by nlinarith
  have hlogy : log y ≤ 2 * t := by
    have := Real.log_le_log (by linarith) hyx2
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogy1 : 1 ≤ log y := by
    have := Real.log_le_log (by linarith) (by linarith : x ≤ y)
    linarith
  have hF1 : (F y : ℝ) ≤ log y ^ c' :=
    hFy.trans (Real.rpow_le_rpow_of_exponent_le hlogy1 hOc)
  have hF2 : log y ^ c' ≤ (2 : ℝ) ^ c' * t ^ c' := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hlogy hc'0
  have htc : 1 ≤ t ^ c' := Real.one_le_rpow ht1 hc'0
  have hsplit : L = t * t ^ c' := by
    rw [hL, Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
  have hmul := mul_le_mul_of_nonneg_right hlx (by linarith : (0 : ℝ) ≤ t ^ c')
  have hKF' : (K : ℝ) ≤ F y := by exact_mod_cast hKF
  nlinarith

theorem erdos_945.variants.equivalence : Erdos945Prop ↔ Erdos945Constant :=
  ⟨prop_to_const, const_to_prop⟩

end Erdos945

#print axioms Erdos945.erdos_945.variants.equivalence
