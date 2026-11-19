import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace Arxiv.«1609.08688»

def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (_hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  classical
  let f : Fin s.length → ℕ × ℕ := fun k => (s[k] 0, s[k] 1)
  let t : Finset (ℕ × ℕ) := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  have ht_card : t.card < (Finset.univ : Finset (Fin s.length)).card := by
    simp only [t, Finset.card_univ, Fintype.card_fin, Finset.card_product,
      Nat.card_Icc, Nat.add_sub_cancel, ← sq]
    exact hs₂
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin s.length)), f k ∈ t := by
    intro k _
    have hmem : s[k] ∈ s := List.getElem_mem k.isLt
    have h0 := hs₁ _ hmem ⟨0, rfl⟩
    have h1 := hs₁ _ hmem ⟨1, rfl⟩
    rw [Set.mem_Icc] at h0 h1
    simp only [t, f, Finset.mem_product, Finset.mem_Icc]
    exact ⟨h0, h1⟩
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht_card hf
  exact ⟨i, j, hij, congrArg Prod.fst hfij, congrArg Prod.snd hfij⟩

lemma bdd (n : ℕ) : BddAbove
    { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) } := by
  refine ⟨(n + 2) ^ 2, ?_⟩
  rintro _ ⟨s, hs_range, hs_inc, rfl⟩
  by_contra hle
  have hs_length : (n + 2) ^ 2 < s.length := Nat.lt_of_not_ge hle
  obtain ⟨i, j, hij, h0, h1⟩ :=
    exists_pair_of_mem_Icc (n := n + 2) (by omega)
      (fun a ha => (hs_range a ha).trans (Set.Icc_subset_Icc_right (by omega))) hs_length
  have hp : s.Pairwise lt₂ := hs_inc
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 (by decide) h0.ge h1.ge)
      (List.pairwise_iff_get.1 hp i j hij)
  · exact (not_lt₂_of_exists 0 1 (by decide) h0.le h1.le)
      (List.pairwise_iff_get.1 hp j i hji)

lemma key {k a b c d : ℕ} (hab : a < b) (hc : c < k) : a * k + c < b * k + d := by
  have := Nat.mul_le_mul_right k (show a + 1 ≤ b from hab)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

lemma nonempty (n : ℕ) :
    { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }.Nonempty :=
  ⟨0, [], by simp, by simp [IsIncreasing₂], rfl⟩

lemma attain (n : ℕ) : ∃ s : List (Fin 3 → ℕ), (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧
    IsIncreasing₂ s ∧ s.length = F n := by
  obtain ⟨s, h1, h2, h3⟩ := Nat.sSup_mem (nonempty n) (bdd n)
  exact ⟨s, h1, h2, h3⟩

lemma le_F {n : ℕ} {s : List (Fin 3 → ℕ)} (h1 : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
    (h2 : IsIncreasing₂ s) : s.length ≤ F n :=
  le_csSup (bdd n) ⟨s, h1, h2, rfl⟩

lemma F_mono {a c : ℕ} (h : a ≤ c) : F a ≤ F c := by
  obtain ⟨s, h1, h2, h3⟩ := attain a
  rw [← h3]
  exact le_F (fun u hu => (h1 u hu).trans (Set.Icc_subset_Icc_right h)) h2

lemma one_le_F : 1 ≤ F 1 := by
  refine le_F (s := [fun _ => 1]) ?_ (by simp [IsIncreasing₂])
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  rintro _ ⟨i, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

/-- Product of two triples: coordinatewise `(u i - 1) * b + v i`. -/
def P (b : ℕ) (u v : Fin 3 → ℕ) : Fin 3 → ℕ := fun i => (u i - 1) * b + v i

def prod (b : ℕ) (s t : List (Fin 3 → ℕ)) : List (Fin 3 → ℕ) :=
  s.flatMap fun u => t.map fun v => P b u v

lemma lt_left {b : ℕ} {u u' v v' : Fin 3 → ℕ} (hv : ∀ i, 1 ≤ v i ∧ v i ≤ b)
    (hv' : ∀ i, 1 ≤ v' i ∧ v' i ≤ b) (hu : ∀ i, 1 ≤ u i) (h : u <₂ u') :
    P b u v <₂ P b u' v' := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  refine ⟨i, j, hij, ?_, ?_⟩
  · have := key (k := b) (c := v i - 1) (d := v' i - 1)
      (show u i - 1 < u' i - 1 by have := hu i; omega) (by have := hv i; omega)
    have := hv i; have := hv' i
    show (u i - 1) * b + v i < (u' i - 1) * b + v' i
    omega
  · have := key (k := b) (c := v j - 1) (d := v' j - 1)
      (show u j - 1 < u' j - 1 by have := hu j; omega) (by have := hv j; omega)
    have := hv j; have := hv' j
    show (u j - 1) * b + v j < (u' j - 1) * b + v' j
    omega

lemma lt_right {b : ℕ} {u v v' : Fin 3 → ℕ} (h : v <₂ v') : P b u v <₂ P b u v' := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  exact ⟨i, j, hij, show (u i - 1) * b + v i < (u i - 1) * b + v' i by omega,
    show (u j - 1) * b + v j < (u j - 1) * b + v' j by omega⟩

lemma prod_range {a b : ℕ} {s t : List (Fin 3 → ℕ)} (hs : ∀ u ∈ s, Set.range u ⊆ Set.Icc 1 a)
    (ht : ∀ v ∈ t, Set.range v ⊆ Set.Icc 1 b) :
    ∀ w ∈ prod b s t, Set.range w ⊆ Set.Icc 1 (a * b) := by
  intro w hw
  simp only [prod, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  rintro _ ⟨i, rfl⟩
  have h1 := hs u hu ⟨i, rfl⟩
  have h2 := ht v hv ⟨i, rfl⟩
  rw [Set.mem_Icc] at h1 h2
  have := Nat.mul_le_mul_right b (show (u i - 1) + 1 ≤ a by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  exact ⟨show 1 ≤ (u i - 1) * b + v i by omega, show (u i - 1) * b + v i ≤ a * b by omega⟩

lemma prod_inc {a b : ℕ} {s t : List (Fin 3 → ℕ)} (hs : ∀ u ∈ s, Set.range u ⊆ Set.Icc 1 a)
    (ht : ∀ v ∈ t, Set.range v ⊆ Set.Icc 1 b) (hs2 : IsIncreasing₂ s) (ht2 : IsIncreasing₂ t) :
    IsIncreasing₂ (prod b s t) := by
  unfold IsIncreasing₂ prod
  rw [List.pairwise_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact ht2.imp fun h => lt_right h
  · refine hs2.imp_of_mem fun {u u'} hu _ h => ?_
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨v', hv', rfl⟩ := hy
    exact lt_left (fun i => ht v hv ⟨i, rfl⟩) (fun i => ht v' hv' ⟨i, rfl⟩)
      (fun i => (hs u hu ⟨i, rfl⟩).1) h

lemma prod_length (b : ℕ) (s t : List (Fin 3 → ℕ)) :
    (prod b s t).length = s.length * t.length := by
  simp [prod, List.length_flatMap]

lemma F_mul (a b : ℕ) : F a * F b ≤ F (a * b) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := attain a
  obtain ⟨t, ht1, ht2, ht3⟩ := attain b
  rw [← hs3, ← ht3, ← prod_length b]
  exact le_F (prod_range hs1 ht1) (prod_inc hs1 ht1 hs2 ht2)

lemma F_pow (n j : ℕ) : F n ^ j ≤ F (n ^ j) := by
  induction j with
  | zero => simpa using one_le_F
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (Nat.mul_le_mul_right _ ih).trans (F_mul _ _)

lemma rpow_pow (n : ℕ) (e : ℝ) (j : ℕ) : ((n ^ j : ℕ) : ℝ) ^ e = ((n : ℝ) ^ e) ^ j := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
    Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]

lemma main_pow {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (j : ℕ) :
    ((n ^ j : ℕ) : ℝ) ^ e ≤ F (n ^ j) := by
  rw [rpow_pow, ← h]
  exact_mod_cast F_pow n j

theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) :
    ∃ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  rw [Filter.frequently_atTop]
  intro N
  exact ⟨n ^ N, (Nat.lt_pow_self hn).le, main_pow h N⟩

theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (b / (e - b))
  rw [Filter.eventually_atTop]
  refine ⟨n ^ J, fun m hm => ?_⟩
  have hn0 : 0 < n := by omega
  have hm0 : m ≠ 0 := by have := pow_pos hn0 J; omega
  have F1 : (1 : ℝ) ≤ F m := by exact_mod_cast one_le_F.trans (F_mono (by omega : 1 ≤ m))
  rcases lt_or_ge b 0 with hb0 | hb0
  · exact (Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm0) hb0.le).trans F1
  · have h1 : n ^ Nat.log n m ≤ m := Nat.pow_log_le_self n hm0
    have h2 : m < n ^ (Nat.log n m + 1) := Nat.lt_pow_succ_log_self hn m
    generalize Nat.log n m = j at h1 h2
    have hjJ : J ≤ j := by
      by_contra hc
      have := Nat.pow_le_pow_right hn0 (show j + 1 ≤ J by omega)
      omega
    have hJ' : (J : ℝ) ≤ j := by exact_mod_cast hjJ
    have heb : 0 < e - b := by linarith
    have key1 : b < J * (e - b) := (div_lt_iff₀ heb).1 hJ
    have key3 : (J : ℝ) * (e - b) ≤ j * (e - b) := mul_le_mul_of_nonneg_right hJ' heb.le
    have key2 : ((j : ℝ) + 1) * b ≤ e * j := by linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
    calc (m : ℝ) ^ b ≤ ((n ^ (j + 1) : ℕ) : ℝ) ^ b :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h2.le) hb0
      _ = (n : ℝ) ^ (((j : ℝ) + 1) * b) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
            Nat.cast_add, Nat.cast_one]
      _ ≤ (n : ℝ) ^ (e * j) := Real.rpow_le_rpow_of_exponent_le hn1 key2
      _ = ((n ^ j : ℕ) : ℝ) ^ e := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm e]
      _ ≤ F (n ^ j) := main_pow h j
      _ ≤ F m := by exact_mod_cast F_mono h1

end Arxiv.«1609.08688»

#print axioms Arxiv.«1609.08688».maximalLength_pow
#print axioms Arxiv.«1609.08688».maximalLength_pow_eventually
