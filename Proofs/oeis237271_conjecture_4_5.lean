import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

namespace OeisA237271

open Nat Finset List

def a (n : ℕ) : ℕ :=
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k
  1 + count

def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k
  1 + num_jumps

lemma pair_iff (n : ℕ) (x : ℕ × ℕ)
    (hx : x ∈ (n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail) :
    (Odd x.2 ∧ x.2 ≥ 2 * x.1) ↔ x.2 > 2 * x.1 := by
  set D := n.divisors.sort (· ≤ ·) with hD
  have hpw : D.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnd : D.Nodup := Finset.sort_nodup _ _
  have hle : ∀ i j (hi : i < D.length) (hj : j < D.length), i ≤ j → D[i] ≤ D[j] := by
    intro i j hi hj hij
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hpw i j hi hj h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen : i + 1 < D.length := by simp at hi; omega
  simp only [List.getElem_zip, List.getElem_tail]
  have hlt : D[i] < D[i + 1] := by
    refine lt_of_le_of_ne (hle i (i + 1) (by omega) hlen (by omega)) ?_
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp heq
    omega
  constructor
  · rintro ⟨ho, hge⟩
    rcases Nat.eq_or_lt_of_le hge with h | h
    · exfalso
      rw [← h] at ho
      exact (Nat.not_even_iff_odd.mpr ho) (even_two_mul _)
    · exact h
  · intro hgt
    refine ⟨?_, hgt.le⟩
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨c, hc⟩ := hev
    have hmem : D[i + 1] ∈ n.divisors := (Finset.mem_sort _).mp (List.getElem_mem hlen)
    rw [Nat.mem_divisors] at hmem
    have hcmem : c ∈ D := by
      rw [hD, Finset.mem_sort, Nat.mem_divisors]
      refine ⟨?_, hmem.2⟩
      exact Nat.dvd_trans ⟨2, by omega⟩ hmem.1
    obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.mp hcmem
    rcases Nat.lt_or_ge i j with h | h
    · have := hle (i + 1) j hlen hj (by omega)
      omega
    · have := hle j i hj (by omega) h
      omega

theorem conjecture_2 (n : ℕ) : a n = num2DenseSublists n := by
  unfold a num2DenseSublists sortedDivisorsList
  simp only
  congr 1
  apply List.countP_congr
  intro x hx
  simp only [decide_eq_true_eq]
  exact pair_iff n x hx

theorem conjecture_3 (n : ℕ) :
    a n = 1 + ((sortedDivisorsList n).zip (sortedDivisorsList n).tail).countP
      fun pair => pair.snd > 2 * pair.fst :=
  conjecture_2 n

namespace P

lemma lt_of_lt {D : List ℕ} (hpw : D.Pairwise (· ≤ ·)) (hnd : D.Nodup) (i j : ℕ)
    (hi : i < D.length) (hj : j < D.length) (hij : i < j) : D[i] < D[j] := by
  refine lt_of_le_of_ne (List.pairwise_iff_getElem.mp hpw i j hi hj hij) ?_
  intro heq
  have := (List.Nodup.getElem_inj_iff hnd).mp heq
  omega

/-- `(x, y)` is a pair of consecutive divisors of `n`. -/
def Cons (n x y : ℕ) : Prop :=
  x ∈ n.divisors ∧ y ∈ n.divisors ∧ x < y ∧ ∀ z ∈ n.divisors, ¬ (x < z ∧ z < y)

lemma mem_zip (n x y : ℕ) :
    (x, y) ∈ (n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail ↔ Cons n x y := by
  set D := n.divisors.sort (· ≤ ·) with hD
  have hpw : D.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnd : D.Nodup := Finset.sort_nodup _ _
  have hmemD : ∀ z, z ∈ D ↔ z ∈ n.divisors := fun z => Finset.mem_sort _
  have hle : ∀ i j (hi : i < D.length) (hj : j < D.length), i ≤ j → D[i] ≤ D[j] := by
    intro i j hi hj hij
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hpw i j hi hj h
  constructor
  · intro hx
    obtain ⟨i, hi, hxy⟩ := List.mem_iff_getElem.mp hx
    have hlen : i + 1 < D.length := by simp at hi; omega
    simp only [List.getElem_zip, List.getElem_tail, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    refine ⟨(hmemD _).mp (List.getElem_mem _), (hmemD _).mp (List.getElem_mem _),
      lt_of_lt hpw hnd i (i + 1) (by omega) hlen (by omega), ?_⟩
    rintro z hz ⟨h1, h2⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hmemD z).mpr hz)
    rcases Nat.lt_or_ge i j with h | h
    · have := hle (i + 1) j hlen hj (by omega); omega
    · have := hle j i hj (by omega) h; omega
  · rintro ⟨hx, hy, hxy, hb⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((hmemD x).mpr hx)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hmemD y).mpr hy)
    have hij : i < j := by
      by_contra h
      push Not at h
      have := hle j i hj hi h
      omega
    have hj' : j = i + 1 := by
      by_contra h
      have h1 := lt_of_lt hpw hnd i (i + 1) hi (by omega) (by omega)
      have h2 := lt_of_lt hpw hnd (i + 1) j (by omega) hj (by omega)
      exact hb _ ((hmemD _).mp (List.getElem_mem _)) ⟨h1, h2⟩
    subst hj'
    refine List.mem_iff_getElem.mpr ⟨i, by simp; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_tail]

lemma zip_nodup (n : ℕ) :
    ((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.map_snd_zip (by simp)]
  exact (Finset.sort_nodup _ _).sublist (List.tail_sublist _)

/-- The jumps: consecutive divisor pairs `(x, y)` with `y > 2x`. -/
noncomputable def S (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (n.divisors ×ˢ n.divisors).filter (fun q => Cons n q.1 q.2 ∧ 2 * q.1 < q.2)

lemma mem_S (n x y : ℕ) : (x, y) ∈ S n ↔ Cons n x y ∧ 2 * x < y := by
  unfold S
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h, h'⟩; exact ⟨⟨h.1, h.2.1⟩, h, h'⟩

lemma count_eq (n : ℕ) :
    ((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).countP
      (fun pair => pair.snd > 2 * pair.fst) = (S n).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((zip_nodup n).filter _)]
  congr 1
  ext ⟨x, y⟩
  rw [List.mem_toFinset, List.mem_filter, mem_zip, mem_S]
  simp only [decide_eq_true_eq]

lemma anti {x y a b n : ℕ} (hx : x * a = n) (hy : y * b = n) (hxy : x < y) (hn : 0 < n) :
    b < a := by
  rcases Nat.lt_or_ge b a with h | h
  · exact h
  exfalso
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hx; omega)
  nlinarith

lemma jump {x y a b n : ℕ} (hx : x * a = n) (hy : y * b = n) (hxy : 2 * x < y) (hn : 0 < n) :
    2 * b < a := by
  rcases Nat.lt_or_ge (2 * b) a with h | h
  · exact h
  exfalso
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hy; omega)
  nlinarith

lemma cons_flip {n x y : ℕ} (hn : 0 < n) (h : Cons n x y) : Cons n (n / y) (n / x) := by
  obtain ⟨hx, hy, hxy, hb⟩ := h
  have hx' := Nat.mem_divisors.mp hx
  have hy' := Nat.mem_divisors.mp hy
  have ex : x * (n / x) = n := Nat.mul_div_cancel' hx'.1
  have ey : y * (n / y) = n := Nat.mul_div_cancel' hy'.1
  refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hy'.1, hn.ne'⟩,
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hx'.1, hn.ne'⟩, anti ex ey hxy hn, ?_⟩
  rintro z hz ⟨h1, h2⟩
  have hz' := Nat.mem_divisors.mp hz
  have ez : z * (n / z) = n := Nat.mul_div_cancel' hz'.1
  have ex' : (n / x) * x = n := by rw [Nat.mul_comm]; exact ex
  have ey' : (n / y) * y = n := by rw [Nat.mul_comm]; exact ey
  exact hb (n / z) (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hz'.1, hn.ne'⟩)
    ⟨anti ez ex' h2 hn, anti ey' ez h1 hn⟩

lemma flip_mem {n x y : ℕ} (hn : 0 < n) (h : (x, y) ∈ S n) : (n / y, n / x) ∈ S n := by
  rw [mem_S] at h ⊢
  obtain ⟨hc, hj⟩ := h
  refine ⟨cons_flip hn hc, ?_⟩
  have ex : x * (n / x) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp hc.1).1
  have ey : y * (n / y) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp hc.2.1).1
  exact jump ex ey hj hn

lemma flip_flip {n x y : ℕ} (hn : 0 < n) (h : (x, y) ∈ S n) :
    (n / (n / x), n / (n / y)) = (x, y) := by
  rw [mem_S] at h
  rw [Nat.div_div_self (Nat.mem_divisors.mp h.1.1).1 hn.ne',
    Nat.div_div_self (Nat.mem_divisors.mp h.1.2.1).1 hn.ne']

lemma prod_lo {x y a b n : ℕ} (hx : x * a = n) (hy : y * b = n) (h : x * y < n) :
    ¬ b * a < n := by
  intro h'
  have key : (x * a) * (y * b) = n * n := by rw [hx, hy]
  have := mul_lt_mul'' h h' (Nat.zero_le _) (Nat.zero_le _)
  nlinarith

lemma prod_hi {x y a b n : ℕ} (hx : x * a = n) (hy : y * b = n) (h : ¬ x * y < n)
    (hne : x * y ≠ n) (hn : 0 < n) : b * a < n := by
  have key : (x * a) * (y * b) = n * n := by rw [hx, hy]
  have h2 : n < x * y := by omega
  by_contra h'
  push Not at h'
  have := mul_lt_mul' h' h2 (Nat.zero_le _) (by omega)
  nlinarith

lemma card_even (n : ℕ) (hn : 0 < n) (hfix : ∀ x y, (x, y) ∈ S n → x * y ≠ n) :
    Even (S n).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := S n) (p := fun q => q.1 * q.2 < n)]
  have : ((S n).filter (fun q => q.1 * q.2 < n)).card =
      ((S n).filter (fun q => ¬ q.1 * q.2 < n)).card := by
    apply Finset.card_nbij' (fun q => (n / q.2, n / q.1)) (fun q => (n / q.2, n / q.1))
    · rintro ⟨x, y⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq ⊢
      refine ⟨flip_mem hn hq.1, ?_⟩
      have hS := (mem_S n x y).mp hq.1
      exact prod_lo (Nat.mul_div_cancel' (Nat.mem_divisors.mp hS.1.1).1)
        (Nat.mul_div_cancel' (Nat.mem_divisors.mp hS.1.2.1).1) hq.2
    · rintro ⟨x, y⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq ⊢
      refine ⟨flip_mem hn hq.1, ?_⟩
      have hS := (mem_S n x y).mp hq.1
      exact prod_hi (Nat.mul_div_cancel' (Nat.mem_divisors.mp hS.1.1).1)
        (Nat.mul_div_cancel' (Nat.mem_divisors.mp hS.1.2.1).1) hq.2 (hfix x y hq.1) hn
    · rintro ⟨x, y⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      exact flip_flip hn hq.1
    · rintro ⟨x, y⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      exact flip_flip hn hq.1
  rw [this]
  exact ⟨_, rfl⟩

lemma odd_a (n : ℕ) (hn : 0 < n) (hfix : ∀ x y, (x, y) ∈ S n → x * y ≠ n) :
    Odd (a n) := by
  rw [conjecture_3, sortedDivisorsList, count_eq]
  obtain ⟨k, hk⟩ := card_even n hn hfix
  exact ⟨k, by omega⟩

end P

theorem conjecture_4 (n : ℕ) (hn : 0 < n) : Odd (a (n ^ 2)) := by
  apply P.odd_a _ (pow_pos hn 2)
  intro x y hS hxy
  rw [P.mem_S] at hS
  obtain ⟨⟨_, _, hlt, hb⟩, _⟩ := hS
  have hmem : n ∈ (n ^ 2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self n two_ne_zero, (pow_pos hn 2).ne'⟩
  rcases Nat.lt_or_ge x n with h1 | h1
  · rcases Nat.lt_or_ge n y with h2 | h2
    · exact hb n hmem ⟨h1, h2⟩
    · nlinarith
  · nlinarith

theorem conjecture_5 (n : ℕ) (hn : 0 < n) : Odd (a (n * (2 * n - 1))) := by
  obtain ⟨k, hk, hk'⟩ : ∃ k, 2 * n - 1 = k ∧ k + 1 = 2 * n := ⟨_, rfl, by omega⟩
  rw [hk]
  have hpos : 0 < n * k := Nat.mul_pos hn (by omega)
  apply P.odd_a _ hpos
  intro x y hS hxy
  rw [P.mem_S] at hS
  obtain ⟨⟨_, _, hlt, hb⟩, hj⟩ := hS
  have hmem : n ∈ (n * k).divisors :=
    Nat.mem_divisors.mpr ⟨Dvd.intro k rfl, hpos.ne'⟩
  rcases Nat.lt_or_ge x n with h1 | h1
  · rcases Nat.lt_or_ge n y with h2 | h2
    · exact hb n hmem ⟨h1, h2⟩
    · nlinarith
  · nlinarith

#print axioms conjecture_4
#print axioms conjecture_5

def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d).card

namespace Q
open P

/-- Consecutive divisor pairs `(x, y)` with `y` odd and `y ≥ 2x`. -/
noncomputable def T (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (n.divisors ×ˢ n.divisors).filter (fun q => Cons n q.1 q.2 ∧ Odd q.2 ∧ q.2 ≥ 2 * q.1)

lemma mem_T (n x y : ℕ) : (x, y) ∈ T n ↔ Cons n x y ∧ Odd y ∧ y ≥ 2 * x := by
  unfold T
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h, h'⟩; exact ⟨⟨h.1, h.2.1⟩, h, h'⟩

lemma count_T (n : ℕ) :
    ((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).countP
      (fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst) = (T n).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((zip_nodup n).filter _)]
  congr 1
  ext ⟨x, y⟩
  rw [List.mem_toFinset, List.mem_filter, mem_zip, mem_T]
  simp only [decide_eq_true_eq]

lemma pred_exists (n m : ℕ) (hn : 0 < n) (hm : m ∈ n.divisors) (h1 : 1 < m) :
    ∃ x, Cons n x m := by
  have hne : (n.divisors.filter (· < m)).Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn.ne', h1⟩⟩
  obtain ⟨hxd, hxm⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  refine ⟨_, hxd, hm, hxm, ?_⟩
  rintro z hz ⟨h2, h3⟩
  have := Finset.le_max' (n.divisors.filter (· < m)) z (Finset.mem_filter.mpr ⟨hz, h3⟩)
  omega

lemma mem_C (n m : ℕ) (hn : 0 < n) :
    (m ∈ n.divisors ∧ Odd m ∧ ¬ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d) ↔
      m = 1 ∨ ∃ x, (x, m) ∈ T n := by
  constructor
  · rintro ⟨hm, ho, hno⟩
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · right
      obtain ⟨x, hx⟩ := pred_exists n m hn hm h1
      refine ⟨x, (mem_T n x m).mpr ⟨hx, ho, ?_⟩⟩
      by_contra hc
      exact hno ⟨x, hx.1, hx.2.2.1, by omega⟩
    · left
      have := Nat.pos_of_mem_divisors hm
      omega
  · rintro (rfl | ⟨x, hx⟩)
    · refine ⟨Nat.one_mem_divisors.mpr hn.ne', odd_one, ?_⟩
      rintro ⟨d, _, h1, h2⟩
      omega
    · rw [mem_T] at hx
      obtain ⟨⟨_, hm, _, hb⟩, ho, h2⟩ := hx
      refine ⟨hm, ho, ?_⟩
      rintro ⟨d, hd, h3, h4⟩
      rcases Nat.lt_or_ge x d with h5 | h5
      · exact hb d hd ⟨h5, h3⟩
      · omega

lemma card_C (n : ℕ) (hn : 0 < n) :
    (n.divisors.filter (fun m => Odd m ∧ ¬ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d)).card =
      (T n).card + 1 := by
  have hC : n.divisors.filter (fun m => Odd m ∧ ¬ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d) =
      insert 1 ((T n).image Prod.snd) := by
    ext m
    rw [Finset.mem_filter, mem_C n m hn, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (h | ⟨x, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(x, m), hx, rfl⟩
    · rintro (h | ⟨⟨x, y⟩, hx, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx⟩
  rw [hC, Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
  · rintro ⟨x, y⟩ hx ⟨x', y'⟩ hx' h
    simp only at h
    subst h
    rw [Finset.mem_coe, mem_T] at hx hx'
    obtain ⟨⟨hxd, _, hxy, hb⟩, _, _⟩ := hx
    obtain ⟨⟨hxd', _, hxy', hb'⟩, _, _⟩ := hx'
    rcases Nat.lt_trichotomy x x' with h | h | h
    · exact absurd ⟨h, hxy'⟩ (hb x' hxd')
    · rw [h]
    · exact absurd ⟨h, hxy⟩ (hb' x hxd)
  · intro h
    obtain ⟨⟨x, y⟩, hx, hy⟩ := Finset.mem_image.mp h
    simp only at hy
    subst hy
    rw [mem_T] at hx
    have := Nat.pos_of_mem_divisors hx.1.1
    have := hx.1.2.2.1
    omega

end Q

theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    a n = A001227 n - A239657 n := by
  have ha : a n = 1 + (Q.T n).card := by
    unfold a
    simp only
    rw [Q.count_T]
  have hA : A001227 n = A239657 n +
      (n.divisors.filter (fun m => Odd m ∧ ¬ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d)).card := by
    unfold A001227 A239657
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : ∃ d ∈ n.divisors, d < m ∧ m < 2 * d
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
    · exact Finset.disjoint_filter.mpr (fun m _ h1 h2 => h2.2 h1.2)
  rw [ha, hA, Q.card_C n hn]
  omega

#print axioms conjecture_1

end OeisA237271
