import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-! Restated from FormalConjecturesForMathlib/NumberTheory/NormalNumber.lean -/

namespace NormalNumber

noncomputable def digitSeq (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b

def IsRichInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℕ), (∀ j, w j < b) → ∃ i, ∀ j : Fin k, digitSeq b x (i + j) = w j

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

lemma coe_fract (x : ℝ) :
    ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
  rw [← Int.self_sub_floor, sub_eq_add_neg, AddCircle.coe_add]
  have : ((-(⌊x⌋ : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨-⌊x⌋, by simp⟩
  rw [this, add_zero]

theorem isRichInBase_iff_dense (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsRichInBase b ξ ↔ Dense (Set.range fun n => (↑((b : ℝ) ^ n * ξ) : AddCircle (1 : ℝ))) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hbpos : (0 : ℝ) < b := by linarith
  constructor
  · intro hrich
    rw [dense_iff_inter_open]
    rintro U hU ⟨p, hp⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective p
    have hV : IsOpen (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' U) :=
      hU.preimage QuotientAddGroup.continuous_mk
    set s := Int.fract t with hsdef
    have hs : s ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' U := by
      show ((s : ℝ) : AddCircle (1 : ℝ)) ∈ U
      rw [hsdef, coe_fract]; exact hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV s hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
      (show (1 : ℝ) / b < 1 by rw [div_lt_one hbpos]; exact hbR)
    let wf : ℕ → ℕ := fun j => ⌊(b : ℝ) ^ (j + 1) * s⌋₊ % b
    have hwf : ∀ j, wf j < b := fun j => Nat.mod_lt _ hb0
    obtain ⟨i, hi⟩ := hrich k (fun j : Fin k => wf j) (fun j => hwf j)
    set y := Int.fract ((b : ℝ) ^ i * ξ) with hydef
    have hs1 : s < 1 := Int.fract_lt_one t
    have hy1 : y < 1 := Int.fract_lt_one _
    have hs0 : 0 ≤ s := Int.fract_nonneg t
    have hy0 : 0 ≤ y := Int.fract_nonneg _
    have hfs : ⌊(b : ℝ) ^ k * s⌋₊ = pre b wf k :=
      (pre_iff b hb0 wf hwf s hs1 k).2 (fun j _ => rfl)
    have hfy : ⌊(b : ℝ) ^ k * y⌋₊ = pre b wf k := by
      refine (pre_iff b hb0 wf hwf y hy1 k).2 (fun j hj => ?_)
      have := hi ⟨j, hj⟩
      rw [digit_eq] at this
      exact this
    have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
    have a1 := Nat.floor_le (mul_nonneg hB.le hs0)
    have a2 := Nat.lt_floor_add_one ((b : ℝ) ^ k * s)
    have a3 := Nat.floor_le (mul_nonneg hB.le hy0)
    have a4 := Nat.lt_floor_add_one ((b : ℝ) ^ k * y)
    rw [hfs] at a1 a2
    rw [hfy] at a3 a4
    have hdist : dist y s < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      have hk' : 1 / (b : ℝ) ^ k < ε := by rw [← one_div_pow]; exact hk
      constructor
      · have : y - s < 1 / (b : ℝ) ^ k := by
          rw [lt_div_iff₀ hB]; nlinarith
        linarith
      · have : s - y < 1 / (b : ℝ) ^ k := by
          rw [lt_div_iff₀ hB]; nlinarith
        linarith
    have hyU : ((y : ℝ) : AddCircle (1 : ℝ)) ∈ U := hball (Metric.mem_ball.2 hdist)
    rw [hydef, coe_fract] at hyU
    exact ⟨_, hyU, i, rfl⟩
  · intro hd k w hw
    let w' : ℕ → ℕ := fun j => if h : j < k then w ⟨j, h⟩ else 0
    have hw' : ∀ j, w' j < b := by
      intro j
      simp only [w']
      split_ifs
      · exact hw _
      · exact hb0
    have hW : pre b w' k < b ^ k := pre_lt b w' hw' k
    set W := pre b w' k with hWdef
    have hB : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbpos k
    have hWR : (W : ℝ) + 1 ≤ (b : ℝ) ^ k := by exact_mod_cast hW
    let I : Set ℝ := Set.Ioo ((W : ℝ) / (b : ℝ) ^ k) (((W : ℝ) + 1) / (b : ℝ) ^ k)
    have hI : IsOpen (((↑) : ℝ → AddCircle (1 : ℝ)) '' I) :=
      QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    have hne : (((↑) : ℝ → AddCircle (1 : ℝ)) '' I).Nonempty := by
      refine ⟨_, ((W : ℝ) + 1 / 2) / (b : ℝ) ^ k, ⟨?_, ?_⟩, rfl⟩
      · rw [div_lt_div_iff_of_pos_right hB]; linarith
      · rw [div_lt_div_iff_of_pos_right hB]; linarith
    obtain ⟨_, ⟨s, ⟨hs1, hs2⟩, hs⟩, ⟨i, rfl⟩⟩ := (dense_iff_inter_open.1 hd) _ hI hne
    have hsW : (W : ℝ) < (b : ℝ) ^ k * s := by
      rw [div_lt_iff₀ hB] at hs1; linarith
    have hsW' : (b : ℝ) ^ k * s < (W : ℝ) + 1 := by
      rw [lt_div_iff₀ hB] at hs2; linarith
    have hs0 : 0 ≤ s := by
      have : (0 : ℝ) ≤ (W : ℝ) / (b : ℝ) ^ k := div_nonneg (Nat.cast_nonneg _) hB.le
      linarith
    have hs01 : s < 1 := by
      have : ((W : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 := by rw [div_le_one hB]; exact hWR
      linarith
    have hy : Int.fract ((b : ℝ) ^ i * ξ) = s := by
      refine (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one _⟩
        ⟨hs0, by simpa using hs01⟩).1 ?_
      rw [coe_fract]; exact hs.symm
    have hfl : ⌊(b : ℝ) ^ k * s⌋₊ = W := by
      rw [Nat.floor_eq_iff (mul_nonneg hB.le hs0)]
      exact ⟨hsW.le, hsW'⟩
    refine ⟨i, fun j => ?_⟩
    rw [digit_eq, hy]
    have := (pre_iff b hb0 w' hw' s hs01 k).1 hfl j j.2
    rw [this]
    simp only [w', dif_pos j.2]

end BugeaudNormalAndRich

#print axioms BugeaudNormalAndRich.isRichInBase_iff_dense
