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

/-- Every positive injective sequence of length `n ≥ 1` has a monotone subsequence
with sum at least `(∑ x) / √n`. -/
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

theorem erdos_1026.variants.lower_bound : 1 / Real.sqrt 2 ∈ admissibleConstants := by
  apply WES.mem_of_le_one
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_le_one (by linarith)]
  exact h1

end Erdos1026

#print axioms Erdos1026.erdos_1026.variants.lower_bound
