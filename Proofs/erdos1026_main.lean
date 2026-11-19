import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt

namespace Erdos1026

open Filter

def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    (∀ i, 0 < x i) →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

namespace WES

variable {n : ℕ} (x : Fin n → ℝ) (r : ℝ → ℝ → Prop)

/-- chain condition along the index order -/
def Ch (I : Finset (Fin n)) : Prop := ∀ a ∈ I, ∀ b ∈ I, a ≤ b → r (x a) (x b)

noncomputable def F (i : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact insert {i} (Finset.univ.filter (fun I => i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ Ch x r I))

lemma mem_F {i : Fin n} {I : Finset (Fin n)} (h : I ∈ F x r i) :
    I = {i} ∨ (i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ Ch x r I) := by
  classical
  unfold F at h
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

lemma mem_F_of {i : Fin n} {I : Finset (Fin n)} (h : i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ Ch x r I) :
    I ∈ F x r i := by
  classical
  unfold F
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr h

lemma single_mem (i : Fin n) : ({i} : Finset (Fin n)) ∈ F x r i := by
  classical
  unfold F
  exact Finset.mem_insert_self _ _

lemma F_ne (i : Fin n) : (F x r i).Nonempty := ⟨_, single_mem x r i⟩

noncomputable def L (i : Fin n) : ℝ := (F x r i).sup' (F_ne x r i) (fun I => ∑ j ∈ I, x j)

lemma cond {i : Fin n} {I : Finset (Fin n)} (hr : ∀ u, r u u) (h : I ∈ F x r i) :
    i ∈ I ∧ (∀ j ∈ I, j ≤ i) ∧ Ch x r I := by
  rcases mem_F x r h with rfl | h
  · refine ⟨Finset.mem_singleton_self _, fun j hj => (Finset.mem_singleton.mp hj).le, ?_⟩
    intro a ha b hb _
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact hr _
  · exact h

lemma x_le (i : Fin n) : x i ≤ L x r i := by
  have := Finset.le_sup' (fun I => ∑ j ∈ I, x j) (single_mem x r i)
  simp only [Finset.sum_singleton] at this
  exact this

lemma attained (i : Fin n) : ∃ I ∈ F x r i, L x r i = ∑ j ∈ I, x j :=
  Finset.exists_mem_eq_sup' (F_ne x r i) _

lemma step (hr : ∀ u, r u u) (ht : ∀ u v w, r u v → r v w → r u w)
    {i j : Fin n} (hij : i < j) (hx : r (x i) (x j)) :
    L x r i + x j ≤ L x r j := by
  obtain ⟨I, hI, hL⟩ := attained x r i
  obtain ⟨hiI, hle, hch⟩ := cond x r hr hI
  have hjI : j ∉ I := fun hj => absurd (hle j hj) (not_le.mpr hij)
  have hmem : insert j I ∈ F x r j := by
    apply mem_F_of
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_rfl
      · exact (hle a ha).trans hij.le
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with ha' | ha' <;>
        rcases Finset.mem_insert.mp hb with hb' | hb'
      · rw [ha', hb']; exact hr _
      · rw [ha'] at hab; exact absurd (hab.trans (hle b hb')) (not_le.mpr hij)
      · rw [hb']; exact ht _ _ _ (hch a ha' i hiI (hle a ha')) hx
      · exact hch a ha' b hb' hab
  have := Finset.le_sup' (fun I => ∑ j ∈ I, x j) hmem
  have hs : ∑ k ∈ insert j I, x k = x j + ∑ k ∈ I, x k := Finset.sum_insert hjI
  simp only [L] at this hL ⊢
  rw [hL]
  linarith

open MeasureTheory in
lemma area {m : ℕ} (x Lf Df : Fin m → ℝ) (Lm Dm : ℝ) (hx' : ∀ i, 0 < x i)
    (hxL : ∀ i, x i ≤ Lf i) (hxD : ∀ i, x i ≤ Df i)
    (hLle : ∀ i, Lf i ≤ Lm) (hDle : ∀ i, Df i ≤ Dm) (hL0 : 0 ≤ Lm) (hD0 : 0 ≤ Dm)
    (hdisj : ∀ i j, i < j → Lf i + x j ≤ Lf j ∨ Df i + x j ≤ Df j) :
    ∑ i, x i * x i ≤ Lm * Dm := by
  let R : Fin m → Set (ℝ × ℝ) := fun i =>
    Set.Ioc (Lf i - x i) (Lf i) ×ˢ Set.Ioc (Df i - x i) (Df i)
  have key : ∀ i j : Fin m, i < j → Disjoint (R i) (R j) := by
    intro i j hij
    rcases hdisj i j hij with h | h
    · refine Set.disjoint_prod.mpr (Or.inl ?_)
      rw [Set.disjoint_left]
      intro p hp hq
      have h1 := hp.2
      have h2 := hq.1
      linarith
    · refine Set.disjoint_prod.mpr (Or.inr ?_)
      rw [Set.disjoint_left]
      intro p hp hq
      have h1 := hp.2
      have h2 := hq.1
      linarith
  have hpd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint R := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin m)), MeasurableSet (R i) :=
    fun i _ => measurableSet_Ioc.prod measurableSet_Ioc
  have hU := measure_biUnion_finset (μ := (volume : Measure (ℝ × ℝ))) hpd hmeas
  have hsub : (⋃ i ∈ (Finset.univ : Finset (Fin m)), R i) ⊆
      Set.Icc 0 Lm ×ˢ Set.Icc 0 Dm := by
    intro p hp
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hi
    have := hLle i
    have := hDle i
    have := hxL i
    have := hxD i
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hvolR : ∀ i, (volume : Measure (ℝ × ℝ)) (R i) = ENNReal.ofReal (x i * x i) := by
    intro i
    show (volume : Measure (ℝ × ℝ)) (Set.Ioc (Lf i - x i) (Lf i) ×ˢ
      Set.Ioc (Df i - x i) (Df i)) = _
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (by linarith [hx' i]), sub_sub_cancel, sub_sub_cancel]
  have hvolB : (volume : Measure (ℝ × ℝ)) (Set.Icc 0 Lm ×ˢ Set.Icc 0 Dm) =
      ENNReal.ofReal (Lm * Dm) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith), sub_zero, sub_zero]
  have hle := measure_mono (μ := (volume : Measure (ℝ × ℝ))) hsub
  rw [hU, hvolB, Finset.sum_congr rfl (fun i _ => hvolR i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (mul_pos (hx' i) (hx' i)).le)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL0 hD0)).mp hle

/-- Cauchy–Schwarz step for arbitrary length `n`. -/
lemma final_gen {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx' : ∀ i, 0 < x i)
    (Lm Dm : ℝ) (hL0 : 0 ≤ Lm) (hD0 : 0 ≤ Dm) (h : ∑ i, x i * x i ≤ Lm * Dm) :
    (∑ i, x i) / Real.sqrt n ≤ Lm ∨ (∑ i, x i) / Real.sqrt n ≤ Dm := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  have hsq : ∑ i, x i ^ 2 = ∑ i, x i * x i := Finset.sum_congr rfl (fun i _ => sq (x i))
  rw [hsq] at hcs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hT : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => (hx' i).le)
  have key : ∀ M : ℝ, 0 ≤ M → Lm * Dm ≤ M * M → (∑ i, x i) / Real.sqrt n ≤ M := by
    intro M hM hLD
    have h1 : (∑ i, x i) ^ 2 ≤ (Real.sqrt n * M) ^ 2 := by
      have e : (Real.sqrt n * M) ^ 2 = (Real.sqrt n * Real.sqrt n) * (M * M) := by ring
      rw [e, hs]
      calc (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i * x i := hcs
        _ ≤ (n : ℝ) * (M * M) :=
          mul_le_mul_of_nonneg_left (h.trans hLD) hnpos.le
    have h2 : ∑ i, x i ≤ Real.sqrt n * M := by
      have h3 : 0 ≤ Real.sqrt n * M := mul_nonneg hspos.le hM
      nlinarith
    rw [div_le_iff₀ hspos]
    linarith
  rcases le_total Dm Lm with hle | hle
  · exact Or.inl (key Lm hL0 (mul_le_mul_of_nonneg_left hle hL0))
  · exact Or.inr (key Dm hD0 (mul_le_mul_of_nonneg_right hle hD0))

lemma main {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) :
    ∃ S ∈ monotonicSubsequenceSums x, (∑ i, x i) / Real.sqrt n ≤ S := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hL0 : 0 ≤ Finset.univ.sup' hne (L x (fun u v => u ≤ v)) :=
    (hx' ⟨0, hn⟩).le.trans ((x_le x _ _).trans
      (Finset.le_sup' (L x (fun u v => u ≤ v)) (Finset.mem_univ _)))
  have hD0 : 0 ≤ Finset.univ.sup' hne (L x (fun u v => v ≤ u)) :=
    (hx' ⟨0, hn⟩).le.trans ((x_le x _ _).trans
      (Finset.le_sup' (L x (fun u v => v ≤ u)) (Finset.mem_univ _)))
  have harea := area x (L x (fun u v => u ≤ v)) (L x (fun u v => v ≤ u)) _ _ hx'
    (fun i => x_le x _ i) (fun i => x_le x _ i)
    (fun i => Finset.le_sup' (L x (fun u v => u ≤ v)) (Finset.mem_univ i))
    (fun i => Finset.le_sup' (L x (fun u v => v ≤ u)) (Finset.mem_univ i)) hL0 hD0
    (by
      intro i j hij
      rcases lt_or_gt_of_ne (hx.ne hij.ne) with h | h
      · exact Or.inl (step x (fun u v => u ≤ v) (fun u => le_refl u)
          (fun u v w h1 h2 => h1.trans h2) hij h.le)
      · exact Or.inr (step x (fun u v => v ≤ u) (fun u => le_refl u)
          (fun u v w h1 h2 => h2.trans h1) hij h.le))
  rcases final_gen hn x hx' _ _ hL0 hD0 harea with h | h
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (L x (fun u v => u ≤ v))
    obtain ⟨I, hI, hIs⟩ := attained x (fun u v => u ≤ v) i
    obtain ⟨_, _, hch⟩ := cond x (fun u v => u ≤ v) (fun u => le_refl u) hI
    refine ⟨∑ j ∈ I, x j, ⟨I, Or.inl (fun a ha b hb hab => hch a ha b hb hab), rfl⟩, ?_⟩
    rw [← hIs, ← hi]
    exact h
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (L x (fun u v => v ≤ u))
    obtain ⟨I, hI, hIs⟩ := attained x (fun u v => v ≤ u) i
    obtain ⟨_, _, hch⟩ := cond x (fun u v => v ≤ u) (fun u => le_refl u) hI
    refine ⟨∑ j ∈ I, x j, ⟨I, Or.inr (fun a ha b hb hab => hch a ha b hb hab), rfl⟩, ?_⟩
    rw [← hIs, ← hi]
    exact h

/-- Every constant `c ≤ 1` is admissible. -/
lemma mem_of_le_one {c : ℝ} (hc : c ≤ 1) : c ∈ admissibleConstants := by
  intro ε hε
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn x hx hx' => ?_⟩
  obtain ⟨S, hS, hle⟩ := main hn x hx hx'
  refine ⟨S, hS, le_trans ?_ hle⟩
  have hT : 0 ≤ (∑ i, x i) / Real.sqrt n :=
    div_nonneg (Finset.sum_nonneg (fun i _ => (hx' i).le)) (Real.sqrt_nonneg _)
  have e : (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) =
      (c - ε) * ((∑ i, x i) / Real.sqrt n) := by ring
  rw [e]
  exact mul_le_of_le_one_left hT (by linarith)

end WES

namespace UB

/-- position value: `k` decreasing blocks of `k` increasing values -/
def v (k i : ℕ) : ℕ := (k - 1 - i / k) * k + i % k

lemma pos_of_lt {k a : ℕ} (ha : a < k ^ 2) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at ha
  · exact h

lemma v_lt {k i : ℕ} (hi : i < k ^ 2) : v k i < k ^ 2 := by
  have hk := pos_of_lt hi
  have hm := Nat.mod_lt i hk
  have h0 := Nat.sub_le (k - 1) (i / k)
  have h1 : k - 1 - i / k + 1 ≤ k := by
    generalize k - 1 - i / k = t at h0 ⊢
    omega
  unfold v
  calc (k - 1 - i / k) * k + i % k < (k - 1 - i / k) * k + k := Nat.add_lt_add_left hm _
    _ = (k - 1 - i / k + 1) * k := (add_one_mul _ _).symm
    _ ≤ k * k := Nat.mul_le_mul_right _ h1
    _ = k ^ 2 := (sq k).symm

lemma cross {k a b : ℕ} (hb : b < k ^ 2) (h : a / k < b / k) : v k b < v k a := by
  have hk := pos_of_lt hb
  have hb' : b < k * k := by rw [← sq]; exact hb
  have hbk : b / k < k := Nat.div_lt_of_lt_mul hb'
  have hm := Nat.mod_lt b hk
  have h1 : k - 1 - b / k + 1 ≤ k - 1 - a / k := by omega
  unfold v
  calc (k - 1 - b / k) * k + b % k < (k - 1 - b / k) * k + k := Nat.add_lt_add_left hm _
    _ = (k - 1 - b / k + 1) * k := (add_one_mul _ _).symm
    _ ≤ (k - 1 - a / k) * k := Nat.mul_le_mul_right _ h1
    _ ≤ (k - 1 - a / k) * k + a % k := Nat.le_add_right _ _

lemma key_anti {k a b : ℕ} (hab : a < b) (hdiv : a / k = b / k) : v k a < v k b := by
  have h1 := Nat.div_add_mod a k
  have h2 := Nat.div_add_mod b k
  rw [hdiv] at h1
  have h3 : a % k < b % k := by
    generalize k * (b / k) = t at h1 h2
    generalize a % k = r at h1 ⊢
    generalize b % k = s at h2 ⊢
    omega
  unfold v
  rw [hdiv]
  exact Nat.add_lt_add_left h3 _

lemma key_mono {k a b : ℕ} (hb : b < k ^ 2) (hab : a < b) (hmod : a % k = b % k) :
    v k b < v k a := by
  apply cross hb
  have hd : a / k ≤ b / k := Nat.div_le_div_right hab.le
  rcases hd.lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 := Nat.div_add_mod a k
    have h2 := Nat.div_add_mod b k
    rw [h, hmod] at h1
    exact absurd (h1.symm.trans h2) hab.ne

lemma v_ne {k a b : ℕ} (hb : b < k ^ 2) (hab : a < b) : v k a ≠ v k b := by
  by_cases h : a / k = b / k
  · exact (key_anti hab h).ne
  · have hd : a / k ≤ b / k := Nat.div_le_div_right hab.le
    exact (cross hb (lt_of_le_of_ne hd h)).ne'

noncomputable def X (k : ℕ) : Fin (k ^ 2) → ℝ := fun i => ((k ^ 3 + v k i.val : ℕ) : ℝ)

lemma X_le_iff (k : ℕ) (a b : Fin (k ^ 2)) : X k a ≤ X k b ↔ v k a.val ≤ v k b.val := by
  show ((k ^ 3 + v k a.val : ℕ) : ℝ) ≤ ((k ^ 3 + v k b.val : ℕ) : ℝ) ↔ _
  rw [Nat.cast_le]
  constructor <;> intro h <;> omega

lemma X_inj (k : ℕ) : Function.Injective (X k) := by
  intro a b hab
  have h : ((k ^ 3 + v k a.val : ℕ) : ℝ) = ((k ^ 3 + v k b.val : ℕ) : ℝ) := hab
  have h' : k ^ 3 + v k a.val = k ^ 3 + v k b.val := by exact_mod_cast h
  have hv : v k a.val = v k b.val := by omega
  rcases lt_trichotomy a.val b.val with hl | hl | hl
  · exact absurd hv (v_ne b.isLt hl)
  · exact Fin.ext hl
  · exact absurd hv.symm (v_ne a.isLt hl)

lemma X_pos (k : ℕ) (hk : 1 ≤ k) (i : Fin (k ^ 2)) : 0 < X k i := by
  have := Nat.one_le_pow 3 k hk
  show (0 : ℝ) < ((k ^ 3 + v k i.val : ℕ) : ℝ)
  exact_mod_cast (show 0 < k ^ 3 + v k i.val by omega)

lemma X_ge (k : ℕ) (i : Fin (k ^ 2)) : (k : ℝ) ^ 3 ≤ X k i := by
  show (k : ℝ) ^ 3 ≤ ((k ^ 3 + v k i.val : ℕ) : ℝ)
  exact_mod_cast (Nat.le_add_right _ _)

lemma X_le (k : ℕ) (i : Fin (k ^ 2)) : X k i ≤ (k : ℝ) ^ 3 + (k : ℝ) ^ 2 := by
  have := v_lt i.isLt
  show ((k ^ 3 + v k i.val : ℕ) : ℝ) ≤ (k : ℝ) ^ 3 + (k : ℝ) ^ 2
  have h : k ^ 3 + v k i.val ≤ k ^ 3 + k ^ 2 := by omega
  exact_mod_cast h

lemma card_le (k : ℕ) (I : Finset (Fin (k ^ 2)))
    (hI : MonotoneOn (X k) ↑I ∨ AntitoneOn (X k) ↑I) : I.card ≤ k := by
  rcases hI with hM | hA
  · have h := Finset.card_le_card_of_injOn (fun i : Fin (k ^ 2) => i.val % k)
      (t := Finset.range k) (by
        intro a _
        have hk := pos_of_lt a.isLt
        simpa using Nat.mod_lt a.val hk) (by
        intro a ha b hb hab
        have hab' : a.val % k = b.val % k := hab
        rcases lt_trichotomy a.val b.val with hl | hl | hl
        · have h1 := key_mono b.isLt hl hab'
          have h2 := (X_le_iff k a b).mp (hM ha hb (Fin.le_iff_val_le_val.mpr hl.le))
          omega
        · exact Fin.ext hl
        · have h1 := key_mono a.isLt hl hab'.symm
          have h2 := (X_le_iff k b a).mp (hM hb ha (Fin.le_iff_val_le_val.mpr hl.le))
          omega)
    rwa [Finset.card_range] at h
  · have h := Finset.card_le_card_of_injOn (fun i : Fin (k ^ 2) => i.val / k)
      (t := Finset.range k) (by
        intro a _
        have ha : a.val < k * k := by rw [← sq]; exact a.isLt
        simpa using Nat.div_lt_of_lt_mul ha) (by
        intro a ha b hb hab
        have hab' : a.val / k = b.val / k := hab
        rcases lt_trichotomy a.val b.val with hl | hl | hl
        · have h1 := key_anti hl hab'
          have h2 := (X_le_iff k b a).mp (hA ha hb (Fin.le_iff_val_le_val.mpr hl.le))
          omega
        · exact Fin.ext hl
        · have h1 := key_anti hl hab'.symm
          have h2 := (X_le_iff k a b).mp (hA hb ha (Fin.le_iff_val_le_val.mpr hl.le))
          omega)
    rwa [Finset.card_range] at h

end UB

theorem erdos_1026.variants.upper_bound : 1 ∈ upperBounds admissibleConstants := by
  intro c hc
  rcases le_or_gt c 1 with h | hlt
  · exact h
  exfalso
  have hc1 : 0 < c - 1 := by linarith
  have hε := hc ((c - 1) / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hε
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (c - 1))
  obtain ⟨k, hkm, hkN⟩ : ∃ k : ℕ, m ≤ k ∧ N0 + 1 ≤ k :=
    ⟨max m (N0 + 1), le_max_left _ _, le_max_right _ _⟩
  have hk1 : 1 ≤ k := by omega
  have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
  have hkN' : N0 ≤ k ^ 2 := by omega
  have hkr : (2 : ℝ) / (c - 1) < k := lt_of_lt_of_le hm (by exact_mod_cast hkm)
  have hkr' : 2 < (k : ℝ) * (c - 1) := (div_lt_iff₀ hc1).mp hkr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  obtain ⟨S, ⟨I, hI, hIS⟩, hle⟩ := hN0 (k ^ 2) hkN' (UB.X k) (UB.X_inj k) (UB.X_pos k hk1)
  have hcard := UB.card_le k I hI
  have hs : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = k := by
    rw [Nat.cast_pow]; exact Real.sqrt_sq (Nat.cast_nonneg k)
  rw [hs, ← hIS] at hle
  have hS : ∑ i ∈ I, UB.X k i ≤ k * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2) := by
    calc ∑ i ∈ I, UB.X k i ≤ ∑ _i ∈ I, ((k : ℝ) ^ 3 + (k : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun i _ => UB.X_le k i)
      _ = (I.card : ℝ) * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (add_nonneg (pow_nonneg hk0.le 3) (pow_nonneg hk0.le 2))
  have hT : (k : ℝ) ^ 5 ≤ ∑ i, UB.X k i := by
    calc (k : ℝ) ^ 5 = ∑ _i : Fin (k ^ 2), (k : ℝ) ^ 3 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
          ring
      _ ≤ ∑ i, UB.X k i := Finset.sum_le_sum (fun i _ => UB.X_ge k i)
  generalize (∑ i, UB.X k i) = T at hle hT
  generalize (∑ i ∈ I, UB.X k i) = S' at hle hS
  have hc' : 0 < c - (c - 1) / 2 := by linarith
  have hle' : (c - (c - 1) / 2) * T / k ≤ S' := by rwa [div_mul_eq_mul_div] at hle
  have hA := (div_le_iff₀ hk0).mp hle'
  have h5 : (c - (c - 1) / 2) * (k : ℝ) ^ 5 ≤ k * (k * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hT hc'.le, mul_le_mul_of_nonneg_left hS hk0.le]
  nlinarith [mul_pos (pow_pos hk0 4) (sub_pos.mpr hkr')]

theorem erdos_1026 : IsGreatest admissibleConstants 1 :=
  ⟨WES.mem_of_le_one le_rfl, erdos_1026.variants.upper_bound⟩

end Erdos1026

#print axioms Erdos1026.erdos_1026.variants.upper_bound
#print axioms Erdos1026.erdos_1026
