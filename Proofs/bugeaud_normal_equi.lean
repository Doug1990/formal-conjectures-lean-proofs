import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

/-! Restated from FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean and
FormalConjecturesForMathlib/Analysis/Equidistribution/ModOne.lean -/

open scoped Topology
open Filter

def IsEquidistributed (a b : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ c d, c ≤ d → Set.Icc c d ⊆ Set.Icc a b →
  Filter.atTop.Tendsto (fun n => ((Finset.range n).filter
    fun m => s m ∈ Set.Icc c d).card / (n : ℝ)) (𝓝 <| (d - c) / (b - a))

def IsEquidistributedModuloOne (s : ℕ → ℝ) : Prop :=
  IsEquidistributed 0 1 (fun n => Int.fract (s n))

namespace NormalNumber

noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

noncomputable def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) →
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).filter (fun i => ∀ j : Fin k, digitSeq b x (i + j) = w j)).card : ℝ) / n)
      atTop
      (nhds (1 / (b : ℝ) ^ k))

end NormalNumber

open NormalNumber

namespace BugeaudNormalAndRich

/-- Value of the first `k` digits `w 0, …, w (k-1)` read in base `b`. -/
def pre (b : ℕ) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => b * pre b w m + w m

lemma pre_lt (b : ℕ) (w : ℕ → ℕ) (hw : ∀ j, w j < b) : ∀ k, pre b w k < b ^ k
  | 0 => by simp [pre]
  | k + 1 => by
    have h1 := Nat.mul_le_mul_left b (Nat.succ_le_of_lt (pre_lt b w hw k))
    have h2 := hw k
    rw [Nat.mul_succ] at h1
    rw [pre, pow_succ, Nat.mul_comm (b ^ k)]
    omega

lemma floor_div_b (b : ℕ) (hb : 0 < b) (z : ℝ) (m : ℕ) :
    ⌊(b : ℝ) ^ (m + 1) * z⌋₊ / b = ⌊(b : ℝ) ^ m * z⌋₊ := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← Nat.floor_div_natCast, pow_succ, mul_comm ((b : ℝ) ^ m) b, mul_assoc,
    mul_div_cancel_left₀ _ hb']

lemma pre_iff (b : ℕ) (hb : 0 < b) (w : ℕ → ℕ) (hw : ∀ j, w j < b) (y : ℝ)
    (hy1 : y < 1) :
    ∀ k, ⌊(b : ℝ) ^ k * y⌋₊ = pre b w k ↔ ∀ j < k, ⌊(b : ℝ) ^ (j + 1) * y⌋₊ % b = w j := by
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, pre]
    constructor
    · intro _ j hj; omega
    · intro _; exact Nat.floor_eq_zero.2 hy1
  | succ k ih =>
    have hd := floor_div_b b hb y k
    constructor
    · intro h j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have h2 : ⌊(b : ℝ) ^ k * y⌋₊ = pre b w k := by
          rw [← hd, h, pre, Nat.mul_add_div hb, Nat.div_eq_of_lt (hw k), add_zero]
        exact (ih.1 h2) j hj
      · rw [h, pre, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt (hw _)]
    · intro h
      have h1 := ih.2 (fun j hj => h j (by omega))
      have h2 := h k (by omega)
      rw [pre, ← h1, ← hd, ← h2]
      exact (Nat.div_add_mod _ _).symm

lemma digit_eq (b : ℕ) (ξ : ℝ) (i j : ℕ) :
    digitSeq b ξ (i + j) = ⌊(b : ℝ) ^ (j + 1) * Int.fract ((b : ℝ) ^ i * ξ)⌋₊ % b := by
  unfold digitSeq
  set z : ℝ := (b : ℝ) ^ i * Int.fract ξ with hzdef
  have hz : 0 ≤ z := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Int.fract_nonneg _)
  have hf : Int.fract ((b : ℝ) ^ i * ξ) = Int.fract z := by
    have e : (b : ℝ) ^ i * ξ = z + (((b : ℤ) ^ i * ⌊ξ⌋ : ℤ) : ℝ) := by
      rw [hzdef, ← Int.self_sub_floor]; push_cast; ring
    rw [e, Int.fract_add_intCast]
  have hz' : (0 : ℤ) ≤ ⌊z⌋ := Int.floor_nonneg.2 hz
  have h3 : ((⌊z⌋.toNat : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz'
  have h4 : z = Int.fract z + ⌊z⌋ := (Int.fract_add_floor z).symm
  have e2 : (b : ℝ) ^ (i + j + 1) * Int.fract ξ
      = (b : ℝ) ^ (j + 1) * Int.fract z + ((b ^ (j + 1) * ⌊z⌋.toNat : ℕ) : ℝ) := by
    push_cast
    rw [h3]
    calc (b : ℝ) ^ (i + j + 1) * Int.fract ξ = (b : ℝ) ^ (j + 1) * z := by
          rw [hzdef]; ring
      _ = (b : ℝ) ^ (j + 1) * (Int.fract z + ⌊z⌋) := by rw [← h4]
      _ = _ := by ring
  have h0 : 0 ≤ (b : ℝ) ^ (j + 1) * Int.fract z :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Int.fract_nonneg _)
  have hdvd : b ∣ b ^ (j + 1) * ⌊z⌋.toNat :=
    dvd_mul_of_dvd_left (dvd_pow_self b (Nat.succ_ne_zero j)) _
  rw [e2, Nat.floor_add_natCast h0, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero,
    Nat.mod_mod, hf]

/-- Extension of a finite word by zeros. -/
def extW {k : ℕ} (w : Fin k → ℕ) : ℕ → ℕ := fun j => if h : j < k then w ⟨j, h⟩ else 0

lemma extW_lt {b k : ℕ} (hb : 0 < b) (w : Fin k → ℕ) (hw : ∀ j, w j < b) :
    ∀ j, extW w j < b := by
  intro j
  unfold extW
  split_ifs
  · exact hw _
  · exact hb

/-- The word `w` occurs at position `i` iff the first `k` digits of `{b^i ξ}` spell `w`. -/
lemma event_iff (b : ℕ) (hb : 0 < b) (ξ : ℝ) (k : ℕ) (w : Fin k → ℕ) (hw : ∀ j, w j < b)
    (i : ℕ) :
    (∀ j : Fin k, digitSeq b ξ (i + j) = w j) ↔
      ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊ = pre b (extW w) k := by
  rw [pre_iff b hb (extW w) (extW_lt hb w hw) (Int.fract ((b : ℝ) ^ i * ξ))
    (Int.fract_lt_one _) k]
  constructor
  · intro h j hj
    have := h ⟨j, hj⟩
    rw [digit_eq] at this
    simp only [extW, dif_pos hj]
    exact this
  · intro h j
    rw [digit_eq, h j j.2]
    simp [extW]

lemma floor_mem (B : ℝ) (hB : 0 < B) (x : ℝ) (W : ℕ) :
    ⌊B * Int.fract x⌋₊ = W ↔ Int.fract x ∈ Set.Ico ((W : ℝ) / B) (((W : ℝ) + 1) / B) := by
  rw [Nat.floor_eq_iff (mul_nonneg hB.le (Int.fract_nonneg x)), Set.mem_Ico, div_le_iff₀ hB,
    lt_div_iff₀ hB]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma card_fiber (R : Finset ℕ) (g : ℕ → ℕ) (S : Finset ℕ) :
    (R.filter fun i => g i ∈ S).card = ∑ W ∈ S, (R.filter fun i => g i = W).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (s := R.filter fun i => g i ∈ S) (t := S)
    (fun x hx => (Finset.mem_filter.1 hx).2)]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [h]; exact hW

/-- Normality gives the frequency of each `b`-adic interval of level `k`. -/
lemma limA (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) (hN : IsNormalInBase b ξ) (k W : ℕ) :
    Tendsto (fun n : ℕ => (((Finset.range n).filter fun i =>
      ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊ = W).card : ℝ) / n) atTop
      (𝓝 (if W < b ^ k then 1 / (b : ℝ) ^ k else 0)) := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
  split_ifs with hW
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (W : ℝ) / (b : ℝ) ^ k := ⟨_, rfl⟩
    have hs1 : s < 1 := by
      rw [hs, div_lt_one hB]; exact_mod_cast hW
    let w : Fin k → ℕ := fun j => ⌊(b : ℝ) ^ ((j : ℕ) + 1) * s⌋₊ % b
    have hw : ∀ j, w j < b := fun j => Nat.mod_lt _ hb0
    have hpre : pre b (extW w) k = W := by
      have h1 := (pre_iff b hb0 (extW w) (extW_lt hb0 w hw) s hs1 k).2
        (fun j hj => by simp only [extW, dif_pos hj, w])
      have h2 : (b : ℝ) ^ k * s = W := by
        rw [hs]; field_simp
      rw [← h1, h2, Nat.floor_natCast]
    have hfil : ∀ n : ℕ, (Finset.range n).filter
          (fun i => ∀ j : Fin k, digitSeq b ξ (i + j) = w j)
        = (Finset.range n).filter
          (fun i => ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊ = W) :=
      fun n => Finset.filter_congr (fun i _ => by rw [event_iff b hb0 ξ k w hw i, hpre])
    exact (hN k w hw).congr (fun n => by rw [hfil n])
  · have h0 : ∀ n : ℕ, ((Finset.range n).filter fun i =>
        ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊ = W).card = 0 := by
      intro n
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ h => hW ?_)
      rw [← h]
      refine (Nat.floor_lt (mul_nonneg hB.le (Int.fract_nonneg _))).2 ?_
      push_cast
      have := Int.fract_lt_one ((b : ℝ) ^ i * ξ)
      nlinarith
    simp only [h0, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds

lemma level (b : ℕ) (hb : 2 ≤ b) (g : ℝ) (hg : 0 < g) : ∃ k : ℕ, 2 / (b : ℝ) ^ k < g := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hg)
    (show (1 : ℝ) / b < 1 by rw [div_lt_one hbpos]; exact hbR)
  refine ⟨k, ?_⟩
  rw [div_pow, one_pow] at hk
  have : 2 / (b : ℝ) ^ k = 2 * (1 / (b : ℝ) ^ k) := by ring
  linarith

/-- Normal implies equidistributed on each closed interval. -/
theorem fwd (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) (hN : IsNormalInBase b ξ) (c d : ℝ) (hcd : c ≤ d)
    (hc : 0 ≤ c) (hd : d ≤ 1) :
    Tendsto (fun n : ℕ => (((Finset.range n).filter fun m =>
      Int.fract ((b : ℝ) ^ m * ξ) ∈ Set.Icc c d).card : ℝ) / n) atTop (𝓝 (d - c)) := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨k, hk⟩ := level b hb (d - c - a) (by linarith)
    have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = Finset.Ico ⌈(b : ℝ) ^ k * c⌉₊ ⌊(b : ℝ) ^ k * d⌋₊ :=
      ⟨_, rfl⟩
    have hSlt : ∀ W ∈ S, W < b ^ k := by
      intro W hW
      rw [hS] at hW
      have h1 := (Finset.mem_Ico.1 hW).2
      have h2 : ⌊(b : ℝ) ^ k * d⌋₊ ≤ b ^ k := Nat.floor_le_of_le (by push_cast; nlinarith)
      omega
    have hlim := tendsto_finsetSum S (fun W _ => limA b hb ξ hN k W)
    have hsum : ∑ W ∈ S, (if W < b ^ k then 1 / (b : ℝ) ^ k else 0)
        = S.card * (1 / (b : ℝ) ^ k) := by
      rw [Finset.sum_congr rfl (fun W hW => if_pos (hSlt W hW)), Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at hlim
    have hcard : a < S.card * (1 / (b : ℝ) ^ k) := by
      have e1 := Nat.lt_floor_add_one ((b : ℝ) ^ k * d)
      have e2 := Nat.ceil_lt_add_one (mul_nonneg hB.le hc)
      have e3 : (⌊(b : ℝ) ^ k * d⌋₊ : ℝ) - ⌈(b : ℝ) ^ k * c⌉₊ ≤ (S.card : ℝ) := by
        rw [hS, Nat.card_Ico]
        rcases le_total ⌈(b : ℝ) ^ k * c⌉₊ ⌊(b : ℝ) ^ k * d⌋₊ with h | h
        · rw [Nat.cast_sub h]
        · rw [Nat.sub_eq_zero_of_le h]
          have := (Nat.cast_le (α := ℝ)).2 h
          simp only [Nat.cast_zero]; linarith
      have e4 : ((b : ℝ) ^ k * d - (b : ℝ) ^ k * c - 2) / (b : ℝ) ^ k
          ≤ (S.card : ℝ) * (1 / (b : ℝ) ^ k) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by linarith) hB.le
      have e5 : ((b : ℝ) ^ k * d - (b : ℝ) ^ k * c - 2) / (b : ℝ) ^ k
          = d - c - 2 / (b : ℝ) ^ k := by field_simp
      linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hcard)] with n hn
    refine lt_of_lt_of_le hn ?_
    have hf := card_fiber (Finset.range n)
      (fun i => ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊) S
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hf]
    refine div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card fun i hi => ?_))
      (Nat.cast_nonneg _)
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have hy0 := Int.fract_nonneg ((b : ℝ) ^ i * ξ)
    have hm := hi.2
    rw [hS, Finset.mem_Ico] at hm
    have f1 := Nat.le_ceil ((b : ℝ) ^ k * c)
    have f2 := Nat.floor_le (mul_nonneg hB.le hy0)
    have f3 := Nat.lt_floor_add_one ((b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ))
    have f4 := Nat.floor_le (mul_nonneg hB.le (hc.trans hcd))
    have g1 := (Nat.cast_le (α := ℝ)).2 hm.1
    have g2 := (Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt hm.2)
    push_cast at g2
    rw [Set.mem_Icc]
    constructor
    · exact le_of_mul_le_mul_left (by linarith) hB
    · exact (lt_of_mul_lt_mul_left (by linarith) hB.le).le
  · obtain ⟨k, hk⟩ := level b hb (a - (d - c)) (by linarith)
    have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = Finset.Icc ⌊(b : ℝ) ^ k * c⌋₊ ⌊(b : ℝ) ^ k * d⌋₊ :=
      ⟨_, rfl⟩
    have hlim := tendsto_finsetSum S (fun W _ => limA b hb ξ hN k W)
    have hsum : ∑ W ∈ S, (if W < b ^ k then 1 / (b : ℝ) ^ k else 0)
        ≤ S.card * (1 / (b : ℝ) ^ k) := by
      calc ∑ W ∈ S, (if W < b ^ k then 1 / (b : ℝ) ^ k else 0)
          ≤ ∑ W ∈ S, 1 / (b : ℝ) ^ k := by
            refine Finset.sum_le_sum fun W _ => ?_
            split_ifs
            · exact le_refl _
            · exact (one_div_pos.2 hB).le
        _ = S.card * (1 / (b : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) * (1 / (b : ℝ) ^ k) < a := by
      have hcd' : (b : ℝ) ^ k * c ≤ (b : ℝ) ^ k * d := by nlinarith
      have hfl : ⌊(b : ℝ) ^ k * c⌋₊ ≤ ⌊(b : ℝ) ^ k * d⌋₊ := Nat.floor_le_floor hcd'
      have e1 := Nat.lt_floor_add_one ((b : ℝ) ^ k * c)
      have e2 := Nat.floor_le (mul_nonneg hB.le (hc.trans hcd))
      have e3 : (S.card : ℝ) = (⌊(b : ℝ) ^ k * d⌋₊ : ℝ) + 1 - ⌊(b : ℝ) ^ k * c⌋₊ := by
        rw [hS, Nat.card_Icc, Nat.cast_sub (by omega)]
        push_cast; ring
      have e4 : (S.card : ℝ) * (1 / (b : ℝ) ^ k)
          ≤ ((b : ℝ) ^ k * d - (b : ℝ) ^ k * c + 2) / (b : ℝ) ^ k := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by linarith) hB.le
      have e5 : ((b : ℝ) ^ k * d - (b : ℝ) ^ k * c + 2) / (b : ℝ) ^ k
          = d - c + 2 / (b : ℝ) ^ k := by field_simp
      linarith
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_of_le_of_lt hsum hcard))] with n hn
    refine lt_of_le_of_lt ?_ hn
    have hf := card_fiber (Finset.range n)
      (fun i => ⌊(b : ℝ) ^ k * Int.fract ((b : ℝ) ^ i * ξ)⌋₊) S
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hf]
    refine div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card fun i hi => ?_))
      (Nat.cast_nonneg _)
    rw [Finset.mem_filter, Set.mem_Icc] at hi
    rw [Finset.mem_filter, hS, Finset.mem_Icc]
    refine ⟨hi.1, Nat.floor_le_floor ?_, Nat.floor_le_floor ?_⟩
    · nlinarith [hi.2.1]
    · nlinarith [hi.2.2]

/-- Equidistribution gives the frequency of half-open subintervals. -/
lemma ico_lim (y : ℕ → ℝ) (hE : IsEquidistributed 0 1 y) (c d : ℝ) (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ 1) :
    Tendsto (fun n : ℕ => (((Finset.range n).filter fun m => y m ∈ Set.Ico c d).card : ℝ) / n)
      atTop (𝓝 (d - c)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rcases lt_or_ge a 0 with h0 | h0
    · exact Filter.Eventually.of_forall fun n =>
        lt_of_lt_of_le h0 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · obtain ⟨e, he⟩ : ∃ e : ℝ, e = c + (a + (d - c)) / 2 := ⟨_, rfl⟩
      have h1 := hE c e (by rw [he]; linarith) (Set.Icc_subset_Icc hc (by rw [he]; linarith))
      rw [sub_zero, div_one] at h1
      have h2 : a < e - c := by rw [he]; linarith
      filter_upwards [h1.eventually (lt_mem_nhds h2)] with n hn
      refine lt_of_lt_of_le hn (div_le_div_of_nonneg_right (Nat.cast_le.2
        (Finset.card_le_card fun i hi => ?_)) (Nat.cast_nonneg _))
      rw [Finset.mem_filter, Set.mem_Icc] at hi
      rw [Finset.mem_filter, Set.mem_Ico]
      exact ⟨hi.1, hi.2.1, by linarith [hi.2.2]⟩
  · have h1 := hE c d hcd.le (Set.Icc_subset_Icc hc hd)
    rw [sub_zero, div_one] at h1
    filter_upwards [h1.eventually (gt_mem_nhds ha)] with n hn
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right (Nat.cast_le.2
        (Finset.card_le_card fun i hi => ?_)) (Nat.cast_nonneg _)) hn
    rw [Finset.mem_filter, Set.mem_Ico] at hi
    rw [Finset.mem_filter, Set.mem_Icc]
    exact ⟨hi.1, hi.2.1, hi.2.2.le⟩

theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * ξ := by
  have hb0 : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  constructor
  · intro hN
    unfold IsEquidistributedModuloOne IsEquidistributed
    intro c d hcd hsub
    have hc : 0 ≤ c := (hsub ⟨le_refl c, hcd⟩).1
    have hd : d ≤ 1 := (hsub ⟨hcd, le_refl d⟩).2
    rw [sub_zero, div_one]
    exact fwd b hb ξ hN c d hcd hc hd
  · intro hE
    unfold IsNormalInBase
    intro k w hw
    have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
    have hW := pre_lt b (extW w) (extW_lt hb0 w hw) k
    have hWR : (pre b (extW w) k : ℝ) + 1 ≤ (b : ℝ) ^ k := by exact_mod_cast hW
    have h := ico_lim (fun m => Int.fract ((b : ℝ) ^ m * ξ)) hE
      ((pre b (extW w) k : ℝ) / (b : ℝ) ^ k) (((pre b (extW w) k : ℝ) + 1) / (b : ℝ) ^ k)
      (div_nonneg (Nat.cast_nonneg _) hB.le)
      (by rw [div_lt_div_iff_of_pos_right hB]; linarith)
      (by rw [div_le_one hB]; exact hWR)
    rw [show ((pre b (extW w) k : ℝ) + 1) / (b : ℝ) ^ k - (pre b (extW w) k : ℝ) / (b : ℝ) ^ k
      = 1 / (b : ℝ) ^ k by ring] at h
    have hfil : ∀ n : ℕ, (Finset.range n).filter
          (fun i => ∀ j : Fin k, digitSeq b ξ (i + j) = w j)
        = (Finset.range n).filter (fun i => Int.fract ((b : ℝ) ^ i * ξ) ∈
          Set.Ico ((pre b (extW w) k : ℝ) / (b : ℝ) ^ k)
            (((pre b (extW w) k : ℝ) + 1) / (b : ℝ) ^ k)) :=
      fun n => Finset.filter_congr (fun i _ =>
        (event_iff b hb0 ξ k w hw i).trans (floor_mem _ hB _ _))
    exact h.congr (fun n => by rw [hfil n])

end BugeaudNormalAndRich

#print axioms BugeaudNormalAndRich.isNormalInBase_iff_isEquidistributedModuloOne
