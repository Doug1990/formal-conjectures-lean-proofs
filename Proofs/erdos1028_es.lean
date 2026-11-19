import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Sqrt

open Filter Asymptotics

namespace Erdos1028

def imbalance (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|

noncomputable def H (n : ℕ) : ℕ :=
  sInf {m | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)}

namespace ES

def sg (b : Bool) : ℤ := if b then 1 else -1

def T {m : ℕ} (a : Fin m → ℤ) (ε : Fin m → Bool) : ℤ := ∑ i, a i * sg (ε i)

lemma sum_cons {m : ℕ} (F : (Fin (m+1) → Bool) → ℤ) :
    ∑ ε, F ε = ∑ ε' : Fin m → Bool, (F (Fin.cons true ε') + F (Fin.cons false ε')) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp F, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

lemma T_cons {m : ℕ} (a : Fin (m+1) → ℤ) (b : Bool) (ε : Fin m → Bool) :
    T a (Fin.cons b ε) = a 0 * sg b + T (Fin.tail a) ε := by
  unfold T
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]

lemma mom (m : ℕ) : ∀ (a : Fin m → ℤ), (∀ i, a i = 1 ∨ a i = -1) → ∀ c : ℤ,
    ∑ ε, (c + T a ε) ^ 2 = 2 ^ m * (c ^ 2 + m) ∧
    ∑ ε, (c + T a ε) ^ 4 = 2 ^ m * (c ^ 4 + 6 * m * c ^ 2 + 3 * m ^ 2 - 2 * m) := by
  induction m with
  | zero =>
    intro a _ c
    simp [T]
  | succ m ih =>
    intro a ha c
    have ha' : ∀ i, Fin.tail a i = 1 ∨ Fin.tail a i = -1 := fun i => ha i.succ
    obtain ⟨p2, p4⟩ := ih (Fin.tail a) ha' (c + 1)
    obtain ⟨q2, q4⟩ := ih (Fin.tail a) ha' (c - 1)
    have e : ∀ k : ℕ, ∑ ε : Fin (m+1) → Bool, (c + T a ε) ^ k
        = ∑ ε, (c + 1 + T (Fin.tail a) ε) ^ k + ∑ ε, (c - 1 + T (Fin.tail a) ε) ^ k := by
      intro k
      rw [sum_cons, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun ε _ => ?_)
      rw [T_cons, T_cons]
      have h1 : a 0 * sg true = a 0 := by simp [sg]
      have h2 : a 0 * sg false = - a 0 := by simp [sg]
      rw [h1, h2]
      set t := T (Fin.tail a) ε
      rcases ha 0 with h | h <;> rw [h]
      · rw [show c + (1 + t) = c + 1 + t by ring, show c + (-1 + t) = c - 1 + t by ring]
      · rw [show c + (-1 + t) = c - 1 + t by ring, show c + (- -1 + t) = c + 1 + t by ring,
          add_comm]
    rw [e 2, e 4, p2, q2, p4, q4]
    constructor
    · push_cast; ring
    · push_cast; ring

lemma avg (m : ℕ) (hm : 1 ≤ m) (a : Fin m → ℤ) (ha : ∀ i, a i = 1 ∨ a i = -1) :
    2 * Real.sqrt m * 2 ^ m ≤ 9 * ∑ ε, |(T a ε : ℝ)| := by
  obtain ⟨h2, h4⟩ := mom m a ha 0
  simp only [zero_add] at h2 h4
  have r2 : ∑ ε, ((T a ε : ℝ)) ^ 2 = 2 ^ m * m := by
    have z : ∑ ε, (T a ε) ^ 2 = 2 ^ m * (m : ℤ) := by rw [h2]; ring
    exact_mod_cast z
  have r4 : ∑ ε, ((T a ε : ℝ)) ^ 4 ≤ 3 * (m : ℝ) ^ 2 * 2 ^ m := by
    have z : ∑ ε, (T a ε) ^ 4 ≤ 3 * (m : ℤ) ^ 2 * 2 ^ m := by
      rw [h4]
      have e : (2 : ℤ) ^ m * (0 ^ 4 + 6 * m * 0 ^ 2 + 3 * m ^ 2 - 2 * m)
          = 3 * (m : ℤ) ^ 2 * 2 ^ m - 2 ^ m * (2 * m) := by ring
      have : (0 : ℤ) ≤ 2 ^ m * (2 * m) := by positivity
      linarith
    exact_mod_cast z
  set q := Real.sqrt m with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hq : q * q = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hK0 : 0 ≤ 3 * q := by positivity
  have pt : ∀ ε, (3 * q) ^ 2 * ((T a ε : ℝ)) ^ 2
      ≤ (3 * q) ^ 3 * |(T a ε : ℝ)| + ((T a ε : ℝ)) ^ 4 := by
    intro ε
    set t : ℝ := (T a ε : ℝ)
    have h0 : 0 ≤ |t| := abs_nonneg t
    rcases le_or_gt |t| (3 * q) with h | h
    · have e : (3 * q) ^ 2 * t ^ 2 = (3 * q) ^ 2 * (|t| * |t|) := by rw [← sq, sq_abs]
      have h3 : (3 * q) ^ 2 * (|t| * |t|) ≤ (3 * q) ^ 2 * ((3 * q) * |t|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h h0) (by positivity)
      have e2 : (3 * q) ^ 2 * ((3 * q) * |t|) = (3 * q) ^ 3 * |t| := by ring
      have : 0 ≤ t ^ 4 := by positivity
      linarith
    · have h5 : (3 * q) ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ hK0 h.le 2
      have h6 : (3 * q) ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg t)
      have e : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have : 0 ≤ (3 * q) ^ 3 * |t| := by positivity
      linarith
  have S1 : ∑ ε, (3 * q) ^ 2 * ((T a ε : ℝ)) ^ 2
      ≤ ∑ ε, ((3 * q) ^ 3 * |(T a ε : ℝ)| + ((T a ε : ℝ)) ^ 4) :=
    Finset.sum_le_sum (fun ε _ => pt ε)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, r2] at S1
  set s := ∑ ε, |(T a ε : ℝ)| with hs
  have main : (3 * q) ^ 2 * (2 ^ m * (q * q)) ≤ (3 * q) ^ 3 * s + 3 * (q * q) ^ 2 * 2 ^ m := by
    rw [hq]; linarith
  have e1 : (3 * q) ^ 2 * (2 ^ m * (q * q)) = 9 * (q ^ 4 * 2 ^ m) := by ring
  have e2 : (3 * q) ^ 3 * s = 27 * (q ^ 3 * s) := by ring
  have e3 : 3 * (q * q) ^ 2 * (2 : ℝ) ^ m = 3 * (q ^ 4 * 2 ^ m) := by ring
  have e4 : 3 * q ^ 3 * (2 * q * 2 ^ m) = 6 * (q ^ 4 * (2 : ℝ) ^ m) := by ring
  have e5 : 3 * q ^ 3 * (9 * s) = 27 * (q ^ 3 * s) := by ring
  have hc : 0 < 3 * q ^ 3 := by positivity
  apply le_of_mul_le_mul_left _ hc
  linarith

lemma T_split {m : ℕ} (g : Fin m → ℤ) (ε : Fin m → Bool) :
    T g ε = ∑ i ∈ Finset.univ.filter (fun i => ε i = true), g i
      - ∑ i ∈ Finset.univ.filter (fun i => ε i = false), g i := by
  unfold T
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases ε i <;> simp [sg]

lemma block_gen (U : Finset ℕ) (t P N : ℕ → ℤ) (h : ∀ u, t u = P u - N u) :
    ∃ V ⊆ U, ∑ u ∈ U, |t u| ≤ 4 * |∑ u ∈ V, P u| ∨ ∑ u ∈ U, |t u| ≤ 4 * |∑ u ∈ V, N u| := by
  have e1 : ∑ u ∈ U.filter (fun u => 0 ≤ t u), |t u|
      = ∑ u ∈ U.filter (fun u => 0 ≤ t u), (P u - N u) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [abs_of_nonneg (Finset.mem_filter.mp hu).2, h]
  have e2 : ∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), |t u|
      = - ∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), (P u - N u) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hu).2), h]
  have e : ∑ u ∈ U, |t u|
      = (∑ u ∈ U.filter (fun u => 0 ≤ t u), P u - ∑ u ∈ U.filter (fun u => 0 ≤ t u), N u)
        - (∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), P u
          - ∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), N u) := by
    rw [← Finset.sum_filter_add_sum_filter_not U (fun u => 0 ≤ t u) (fun u => |t u|), e1, e2,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2⟩ := hc _ (Finset.filter_subset (fun u => 0 ≤ t u) U)
  obtain ⟨c3, c4⟩ := hc _ (Finset.filter_subset (fun u => ¬ 0 ≤ t u) U)
  have d1 := le_abs_self (∑ u ∈ U.filter (fun u => 0 ≤ t u), P u)
  have d2 := neg_abs_le (∑ u ∈ U.filter (fun u => 0 ≤ t u), N u)
  have d3 := neg_abs_le (∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), P u)
  have d4 := le_abs_self (∑ u ∈ U.filter (fun u => ¬ 0 ≤ t u), N u)
  have d0 : 0 ≤ ∑ u ∈ U, |t u| := Finset.sum_nonneg (fun u _ => abs_nonneg _)
  linarith

def S (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ := ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y

lemma S_union (f : ℕ → ℕ → ℤ) (U V : Finset ℕ) (h : ∀ x ∈ U, ∀ y ∈ V, x < y) :
    S f (U ∪ V) = S f U + S f V + ∑ x ∈ U, ∑ y ∈ V, f x y := by
  have hd : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact lt_irrefl a (h a ha a hb)
  unfold S
  rw [Finset.sum_union hd]
  have h1 : ∀ x ∈ U, ∑ y ∈ (U ∪ V).filter (fun y => x < y), f x y
      = ∑ y ∈ U.filter (fun y => x < y), f x y + ∑ y ∈ V, f x y := by
    intro x hx
    rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hd)]
    congr 1
    rw [Finset.filter_true_of_mem]
    intro y hy
    exact h x hx y hy
  have h2 : ∀ x ∈ V, ∑ y ∈ (U ∪ V).filter (fun y => x < y), f x y
      = ∑ y ∈ V.filter (fun y => x < y), f x y := by
    intro x hx
    rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hd)]
    rw [Finset.filter_false_of_mem, Finset.sum_empty, zero_add]
    intro y hy hxy
    exact lt_asymm hxy (h y hy x hx)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

lemma abs_S_le (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (X : Finset ℕ) :
    |S f X| ≤ (X.card : ℤ) * X.card := by
  unfold S
  calc |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|
      ≤ ∑ x ∈ X, |∑ y ∈ X.filter (fun y => x < y), f x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ X, ∑ y ∈ X, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro x _
        calc |∑ y ∈ X.filter (fun y => x < y), f x y|
            ≤ ∑ y ∈ X.filter (fun y => x < y), |f x y| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ y ∈ X.filter (fun y => x < y), (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro y _
              rcases hf x y with h | h <;> simp [h]
          _ ≤ ∑ y ∈ X, (1 : ℤ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by norm_num)
    _ = (X.card : ℤ) * X.card := by simp

lemma nonempty (n : ℕ) : (n * n) ∈ {m : ℕ | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)} := by
  refine ⟨fun _ _ => 1, fun _ _ => Or.inl rfl, ?_⟩
  intro X hX
  have h1 := abs_S_le (fun _ _ => 1) (fun _ _ => Or.inl rfl) X
  have h2 : X.card ≤ n := by
    have := Finset.card_le_card hX
    simpa using this
  have h3 : (X.card : ℤ) ≤ n := by exact_mod_cast h2
  have h4 : (0 : ℤ) ≤ X.card := by positivity
  have h5 : imbalance (fun _ _ => 1) X = |S (fun _ _ => 1) X| := rfl
  rw [h5]
  push_cast
  nlinarith

def w (m : ℕ) (i : Fin m) : ℕ := m + 1 + (i : ℕ)

def D (f : ℕ → ℕ → ℤ) (m : ℕ) (V : Finset ℕ) (I : Finset (Fin m)) : ℤ :=
  ∑ u ∈ V, ∑ i ∈ I, f u (w m i)

lemma cross (n m : ℕ) (hmn : 2 * m ≤ n) (f : ℕ → ℕ → ℤ) (M : ℤ)
    (hM : ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ M)
    (V : Finset ℕ) (hV : V ⊆ Finset.Icc 1 m) (I : Finset (Fin m)) : |D f m V I| ≤ 3 * M := by
  have winj : ∀ i ∈ I, ∀ j ∈ I, w m i = w m j → i = j := by
    intro i _ j _ h
    unfold w at h
    exact Fin.ext (by omega)
  have hD : D f m V I = ∑ x ∈ V, ∑ y ∈ I.image (w m), f x y := by
    unfold D
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_image winj]
  have hlt : ∀ x ∈ V, ∀ y ∈ I.image (w m), x < y := by
    intro x hx y hy
    have := Finset.mem_Icc.mp (hV hx)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    unfold w; omega
  have hWs : I.image (w m) ⊆ Finset.Icc 1 n := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    have := i.isLt
    unfold w
    rw [Finset.mem_Icc]; omega
  have hVs : V ⊆ Finset.Icc 1 n := hV.trans (Finset.Icc_subset_Icc_right (by omega))
  have hU := S_union f V (I.image (w m)) hlt
  have a1 : |S f (V ∪ I.image (w m))| ≤ M := hM _ (Finset.union_subset hVs hWs)
  have a2 : |S f V| ≤ M := hM _ hVs
  have a3 : |S f (I.image (w m))| ≤ M := hM _ hWs
  rw [hD]
  have b1 := abs_le.mp a1
  have b2 := abs_le.mp a2
  have b3 := abs_le.mp a3
  rw [abs_le]
  constructor <;> linarith

lemma key (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℕ → ℤ) (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (M : ℤ)
    (hM : ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ M) : (n : ℝ) * Real.sqrt n ≤ 324 * M := by
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hmn : 2 * m ≤ n := by omega
  have hn3 : n ≤ 3 * m := by omega
  have hav : ∀ u, 2 * Real.sqrt m * 2 ^ m
      ≤ 9 * ∑ ε, |((T (fun i : Fin m => f u (w m i)) ε : ℤ) : ℝ)| :=
    fun u => avg m hm1 _ (fun i => hf _ _)
  have h1 := Finset.sum_le_sum (s := Finset.Icc 1 m) (fun u _ => hav u)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_comm] at h1
  obtain ⟨ε, hε⟩ : ∃ ε : Fin m → Bool, 2 * (m : ℝ) * Real.sqrt m
      ≤ 9 * ∑ u ∈ Finset.Icc 1 m, |((T (fun i : Fin m => f u (w m i)) ε : ℤ) : ℝ)| := by
    by_contra hc
    push Not at hc
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin m → Bool))
      (fun ε _ => hc ε)
    rw [← Finset.mul_sum] at hlt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul] at hlt
    push_cast at hlt
    have e1 : (m : ℝ) * (2 * Real.sqrt m * 2 ^ m) = 2 ^ m * (2 * m * Real.sqrt m) := by ring
    linarith
  obtain ⟨V, hV, hor⟩ := block_gen (Finset.Icc 1 m)
    (fun u => T (fun i : Fin m => f u (w m i)) ε)
    (fun u => ∑ i ∈ Finset.univ.filter (fun i => ε i = true), f u (w m i))
    (fun u => ∑ i ∈ Finset.univ.filter (fun i => ε i = false), f u (w m i))
    (fun u => T_split _ ε)
  have c1 : |∑ u ∈ V, ∑ i ∈ Finset.univ.filter (fun i => ε i = true), f u (w m i)| ≤ 3 * M :=
    cross n m hmn f M hM V hV _
  have c2 : |∑ u ∈ V, ∑ i ∈ Finset.univ.filter (fun i => ε i = false), f u (w m i)| ≤ 3 * M :=
    cross n m hmn f M hM V hV _
  have hR : ∑ u ∈ Finset.Icc 1 m, |T (fun i : Fin m => f u (w m i)) ε| ≤ 12 * M := by
    rcases hor with h | h <;> linarith
  have hR' : ∑ u ∈ Finset.Icc 1 m, |((T (fun i : Fin m => f u (w m i)) ε : ℤ) : ℝ)|
      ≤ 12 * (M : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hR
    push_cast at this
    exact this
  set q := Real.sqrt m with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = (m : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hsq : Real.sqrt n ≤ 2 * q := by
    have h4 : (n : ℝ) ≤ (2 * q) * (2 * q) := by
      rw [show (2 * q) * (2 * q) = 4 * (q * q) by ring, hqq]
      exact_mod_cast (by omega : n ≤ 4 * m)
    calc Real.sqrt n ≤ Real.sqrt ((2 * q) * (2 * q)) := Real.sqrt_le_sqrt h4
      _ = 2 * q := Real.sqrt_mul_self (by positivity)
  have hn3' : (n : ℝ) ≤ 3 * m := by exact_mod_cast hn3
  have hprod : (n : ℝ) * Real.sqrt n ≤ (3 * m) * (2 * q) :=
    mul_le_mul hn3' hsq (Real.sqrt_nonneg _) (by positivity)
  have e2 : (3 * (m : ℝ)) * (2 * q) = 3 * (2 * (m : ℝ) * q) := by ring
  linarith

end ES

theorem erdos_1028.variants.erdos_spencer :
    (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) =O[atTop] (fun n => (H n : ℝ)) := by
  apply IsBigO.of_bound 324
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨f, hf, hm⟩ := Nat.sInf_mem ⟨_, ES.nonempty n⟩
  have k := ES.key n hn f hf (H n : ℤ) hm
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have e : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), e]
  push_cast at k
  exact k

namespace UB

/-- one factor of the Sylvester–Hadamard sign -/
def s (a b : Bool) : ℤ := if (a && b) then -1 else 1

def h {k : ℕ} (u v : Fin k → Bool) : ℤ := ∏ i, s (u i) (v i)

lemma s_pair (a a' : Bool) : ∑ b : Bool, s a b * s a' b = if a = a' then 2 else 0 := by
  rw [Fintype.sum_bool]
  cases a <;> cases a' <;> simp [s]

lemma s_sq (a b : Bool) : s a b * s a b = 1 := by
  cases a <;> cases b <;> simp [s]

lemma s_comm (a b : Bool) : s a b = s b a := by
  cases a <;> cases b <;> rfl

lemma h_comm {k : ℕ} (u v : Fin k → Bool) : h u v = h v u := by
  unfold h; exact Finset.prod_congr rfl (fun i _ => s_comm _ _)

lemma h_sq {k : ℕ} (u v : Fin k → Bool) : h u v * h u v = 1 := by
  unfold h
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => s_sq _ _)

lemma h_pm {k : ℕ} (u v : Fin k → Bool) : h u v = 1 ∨ h u v = -1 :=
  mul_self_eq_one_iff.mp (h_sq u v)

/-- orthogonality of the rows -/
lemma orth {k : ℕ} (u u' : Fin k → Bool) :
    ∑ v : Fin k → Bool, h u v * h u' v = if u = u' then 2 ^ k else 0 := by
  have e1 : ∀ v : Fin k → Bool, h u v * h u' v = ∏ i, (s (u i) (v i) * s (u' i) (v i)) := by
    intro v; unfold h; rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun v _ => e1 v)]
  rw [← Fintype.prod_sum (fun i b => s (u i) b * s (u' i) b)]
  simp only [s_pair]
  split_ifs with hu
  · subst hu
    simp
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ u' i := by
      by_contra hc
      push Not at hc
      exact hu (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Lindsey's lemma for the Hadamard matrix -/
lemma lindsey {k : ℕ} (X : Finset ℕ) (φ : ℕ → Fin k → Bool) (hφ : Set.InjOn φ X) :
    (∑ x ∈ X, ∑ y ∈ X, h (φ x) (φ y)) ^ 2 ≤ (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) := by
  set R : (Fin k → Bool) → ℤ := fun v => ∑ x ∈ X, h (φ x) v with hR
  have e1 : ∑ x ∈ X, ∑ y ∈ X, h (φ x) (φ y) = ∑ y ∈ X, R (φ y) := by
    rw [Finset.sum_comm]
  rw [e1]
  have cs := sq_sum_le_card_mul_sum_sq (s := X) (f := fun y => R (φ y))
  refine le_trans cs ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e2 : ∑ y ∈ X, R (φ y) ^ 2 = ∑ v ∈ X.image φ, R v ^ 2 := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hφ ha hb hab
  rw [e2]
  have e3 : ∑ v ∈ X.image φ, R v ^ 2 ≤ ∑ v, R v ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun v => sq_nonneg _)
  refine le_trans e3 (le_of_eq ?_)
  have e4 : ∀ v, R v ^ 2 = ∑ x ∈ X, ∑ x' ∈ X, h (φ x) v * h (φ x') v := by
    intro v
    rw [hR, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun v _ => e4 v), Finset.sum_comm]
  have e5 : ∀ x ∈ X, ∑ v, ∑ x' ∈ X, h (φ x) v * h (φ x') v = 2 ^ k := by
    intro x hx
    rw [Finset.sum_comm]
    simp only [orth]
    have : ∀ x' ∈ X, (if φ x = φ x' then (2 : ℤ) ^ k else 0) = if x = x' then 2 ^ k else 0 := by
      intro x' hx'
      by_cases hxx : x = x'
      · subst hxx; simp
      · rw [if_neg hxx, if_neg (fun h' => hxx (hφ hx hx' h'))]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hx]
  rw [Finset.sum_congr rfl e5]
  simp

/-- splitting the full double sum of a symmetric function -/
lemma split (g : ℕ → ℕ → ℤ) (hg : ∀ x y, g x y = g y x) (X : Finset ℕ) :
    ∑ x ∈ X, ∑ y ∈ X, g x y
      = 2 * ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y + ∑ x ∈ X, g x x := by
  have pt : ∀ x y, g x y = (if x < y then g x y else 0) + (if y < x then g x y else 0)
      + (if x = y then g x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · rw [if_pos hxy, if_neg (lt_asymm hxy), if_neg (ne_of_lt hxy)]; ring
    · subst hxy; simp
    · rw [if_neg (lt_asymm hxy), if_pos hxy, if_neg (ne_of_gt hxy)]; ring
  have A : ∑ x ∈ X, ∑ y ∈ X, g x y = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0)
      + ∑ x ∈ X, ∑ y ∈ X, (if y < x then g x y else 0)
      + ∑ x ∈ X, ∑ y ∈ X, (if x = y then g x y else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => pt x y)
  have B : ∑ x ∈ X, ∑ y ∈ X, (if y < x then g x y else 0)
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hg]
  have C : ∑ x ∈ X, ∑ y ∈ X, (if x = y then g x y else 0) = ∑ x ∈ X, g x x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_ite_eq]
    simp [hx]
  have D : ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), g x y
      = ∑ x ∈ X, ∑ y ∈ X, (if x < y then g x y else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_filter]
  rw [A, B, C, D]
  ring

def φ (k : ℕ) (x : ℕ) : Fin k → Bool := fun i => x.testBit i

def F (k : ℕ) (x y : ℕ) : ℤ := h (φ k x) (φ k y)

lemma φ_inj (k n : ℕ) (hn : n < 2 ^ k) : Set.InjOn (φ k) (Finset.Icc 1 n : Set ℕ) := by
  intro x hx y hy hxy
  simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun hxy ⟨i, hi⟩
  · have hk : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

lemma imb_bound (k n : ℕ) (hn : n < 2 ^ k) (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 n) :
    imbalance (F k) X ≤ ((Nat.sqrt (n * n * 2 ^ k) + n : ℕ) : ℤ) := by
  have inj : Set.InjOn (φ k) (X : Set ℕ) := (φ_inj k n hn).mono (Finset.coe_subset.mpr hX)
  have hc : (X.card : ℤ) ≤ n := by
    have := Finset.card_le_card hX
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have L : (∑ x ∈ X, ∑ y ∈ X, F k x y) ^ 2 ≤ (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) :=
    lindsey X (φ k) inj
  have Sp := split (F k) (fun x y => h_comm _ _) X
  have hD : |∑ x ∈ X, F k x x| ≤ X.card := by
    calc |∑ x ∈ X, F k x x| ≤ ∑ x ∈ X, |F k x x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ X, (1 : ℤ) := Finset.sum_congr rfl (fun x _ => by
          rcases h_pm (φ k x) (φ k x) with h' | h' <;> simp [F, h'])
      _ = X.card := by simp
  set S := ∑ x ∈ X, ∑ y ∈ X, F k x y with hS
  set D := ∑ x ∈ X, F k x x with hDdef
  set r := Nat.sqrt (n * n * 2 ^ k) with hr
  have hr1 : ((n * n * 2 ^ k : ℕ) : ℤ) < (((r + 1) * (r + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_succ_sqrt (n * n * 2 ^ k)
  push_cast at hr1
  have h0 : (0 : ℤ) ≤ X.card := by positivity
  have hXn : (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) ≤ n * (n * 2 ^ k) := by
    have h2 : (0 : ℤ) < 2 ^ k := by positivity
    have h3 : (X.card : ℤ) * 2 ^ k ≤ n * 2 ^ k := mul_le_mul_of_nonneg_right hc h2.le
    calc (X.card : ℤ) * ((X.card : ℤ) * 2 ^ k) ≤ n * ((X.card : ℤ) * 2 ^ k) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ n * (n * 2 ^ k) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hSr : |S| ≤ (r : ℤ) := by
    by_contra hcon
    push Not at hcon
    have hr0 : (0 : ℤ) ≤ (r : ℤ) + 1 := by positivity
    have : ((r : ℤ) + 1) * ((r : ℤ) + 1) ≤ |S| * |S| := mul_self_le_mul_self hr0 (by omega)
    have hsq : |S| * |S| = S ^ 2 := by rw [← sq, sq_abs]
    nlinarith
  unfold imbalance
  push_cast
  have a1 := abs_le.mp hSr
  have a2 := abs_le.mp hD
  have hr0 : (0 : ℤ) ≤ r := by positivity
  rw [abs_le]
  constructor <;> linarith

end UB

theorem erdos_1028.variants.upper_bound :
    (fun n => (H n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop 1] with n hn
  set k := Nat.log 2 n + 1 with hkdef
  have hk1 : n < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk2 : 2 ^ k ≤ 2 * n := by
    have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    rw [hkdef, pow_succ]; omega
  have hH : H n ≤ Nat.sqrt (n * n * 2 ^ k) + n := by
    apply Nat.sInf_le
    exact ⟨UB.F k, fun x y => UB.h_pm _ _, fun X hX => UB.imb_bound k n hk1 X hX⟩
  set r := Nat.sqrt (n * n * 2 ^ k) with hrdef
  have hr : r * r ≤ n * n * (2 * n) :=
    le_trans (Nat.sqrt_le (n * n * 2 ^ k)) (Nat.mul_le_mul_left _ hk2)
  have hrR : (r : ℝ) * r ≤ 2 * (n : ℝ) ^ 3 := by
    have := (by exact_mod_cast hr : ((r * r : ℕ) : ℝ) ≤ ((n * n * (2 * n) : ℕ) : ℝ))
    push_cast at this
    nlinarith
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t := (n : ℝ) ^ (3 / 2 : ℝ) with htdef
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t * t = (n : ℝ) ^ 3 := by
    rw [htdef, ← Real.rpow_add hpos, show (3 / 2 : ℝ) + 3 / 2 = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hnt : (n : ℝ) ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  have hrt : (r : ℝ) ≤ 2 * t := by
    by_contra hc
    push Not at hc
    have : (2 * t) * (2 * t) < r * r := mul_self_lt_mul_self (by positivity) hc
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg ht0]
  have : (H n : ℝ) ≤ r + n := by exact_mod_cast hH
  linarith

theorem erdos_1028 :
    (fun n => (H n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) :=
  ⟨erdos_1028.variants.upper_bound, erdos_1028.variants.erdos_spencer⟩

end Erdos1028

#print axioms Erdos1028.erdos_1028.variants.erdos_spencer
#print axioms Erdos1028.erdos_1028
