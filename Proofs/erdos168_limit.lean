import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic

open scoped Topology
open Finset Filter

namespace Erdos168

/-- Restated from the checkout (ErdosProblems/168.lean). -/
def NonTernary (S : Finset ℕ) : Prop := ∀ n : ℕ, n ∉ S ∨ 2*n ∉ S ∨ 3*n ∉ S

def IntervalNonTernarySets (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    fun S => ∀ n ∈ Finset.Icc 1 (N / 3 : ℕ), n ∉ S ∨ 2*n ∉ S ∨ 3*n ∉ S

abbrev F (N : ℕ) : ℕ := (IntervalNonTernarySets N).sup Finset.card

lemma mem_IntervalNonTernarySets_iff (N : ℕ) (S : Finset ℕ) :
    S ∈ IntervalNonTernarySets N ↔ NonTernary S ∧ S ⊆ Finset.Icc 1 N := by
  refine ⟨fun h => ?_, fun h => by simpa [h, IntervalNonTernarySets] using fun _ _ _ => h.1 _⟩
  simp_all [NonTernary, IntervalNonTernarySets, S.subset_iff, Nat.le_div_iff_mul_le, mul_comm,
      or_iff_not_imp_left]
  exact fun n hn₁ hn₂ hn₃ => h.2 n (h.1 hn₁).1 (h.1 hn₃).2 hn₁ hn₂ hn₃

namespace GS

open Classical

noncomputable section

def ok (m : ℕ) : Prop := ¬ 2 ∣ m ∧ ¬ 3 ∣ m

lemma ok_ne {m : ℕ} (hm : ok m) : m ≠ 0 := by rintro rfl; exact hm.1 (dvd_zero 2)

lemma fac2 {m : ℕ} (a b : ℕ) (hm : ok m) : (m * 2 ^ a * 3 ^ b).factorization 2 = a := by
  have h0 := ok_ne hm
  have e1 : (2:ℕ).factorization 2 = 1 := Nat.prime_two.factorization_self
  have e2 : (3:ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have e3 := Nat.factorization_eq_zero_of_not_dvd hm.1
  rw [Nat.factorization_mul (mul_ne_zero h0 (by positivity)) (by positivity),
    Nat.factorization_mul h0 (by positivity)]
  simp [Nat.factorization_pow, e1, e2, e3]

lemma fac3 {m : ℕ} (a b : ℕ) (hm : ok m) : (m * 2 ^ a * 3 ^ b).factorization 3 = b := by
  have h0 := ok_ne hm
  have e1 : (3:ℕ).factorization 3 = 1 := Nat.prime_three.factorization_self
  have e2 : (2:ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have e3 := Nat.factorization_eq_zero_of_not_dvd hm.2
  rw [Nat.factorization_mul (mul_ne_zero h0 (by positivity)) (by positivity),
    Nat.factorization_mul h0 (by positivity)]
  simp [Nat.factorization_pow, e1, e2, e3]

lemma uniq {m m' a a' b b' : ℕ} (hm : ok m) (hm' : ok m')
    (h : m * 2 ^ a * 3 ^ b = m' * 2 ^ a' * 3 ^ b') : m = m' ∧ a = a' ∧ b = b' := by
  have ha : a = a' := by rw [← fac2 a b hm, h, fac2 a' b' hm']
  have hb : b = b' := by rw [← fac3 a b hm, h, fac3 a' b' hm']
  subst ha; subst hb
  refine ⟨?_, rfl, rfl⟩
  have : (0:ℕ) < 2 ^ a * 3 ^ b := by positivity
  rw [mul_assoc, mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right this h

lemma ok_one : ok 1 := ⟨by norm_num, by norm_num⟩

lemma uniq1 {a a' b b' : ℕ} (h : 2 ^ a * 3 ^ b = 2 ^ a' * 3 ^ b') : a = a' ∧ b = b' := by
  have := uniq (a := a) (a' := a') (b := b) (b' := b') ok_one ok_one (by simpa using h)
  exact this.2

lemma exists_dec (n : ℕ) (hn : 0 < n) : ∃ m a b, ok m ∧ n = m * 2 ^ a * 3 ^ b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h2 : 2 ∣ n
    · obtain ⟨k, rfl⟩ := h2
      obtain ⟨m, a, b, hm, hk⟩ := ih k (by omega) (by omega)
      exact ⟨m, a + 1, b, hm, by rw [hk]; ring⟩
    · by_cases h3 : 3 ∣ n
      · obtain ⟨k, rfl⟩ := h3
        obtain ⟨m, a, b, hm, hk⟩ := ih k (by omega) (by omega)
        exact ⟨m, a, b + 1, hm, by rw [hk]; ring⟩
      · exact ⟨n, 0, 0, ⟨h2, h3⟩, by ring⟩

/-- The grid of exponent pairs with `2^a 3^b ≤ k`. -/
def G (k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (k + 1)) ×ˢ (range (k + 1))).filter (fun p => 2 ^ p.1 * 3 ^ p.2 ≤ k)

lemma mem_G {k : ℕ} {p : ℕ × ℕ} : p ∈ G k ↔ 2 ^ p.1 * 3 ^ p.2 ≤ k := by
  unfold G
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have h1 : p.1 < 2 ^ p.1 := Nat.lt_pow_self (by norm_num)
    have h2 : p.2 < 3 ^ p.2 := Nat.lt_pow_self (by norm_num)
    have h3 : 1 ≤ 3 ^ p.2 := Nat.one_le_pow _ _ (by norm_num)
    have h4 : 1 ≤ 2 ^ p.1 := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨⟨?_, ?_⟩, h⟩ <;> nlinarith

def Good (P : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b, (a, b) ∉ P ∨ (a + 1, b) ∉ P ∨ (a, b + 1) ∉ P

lemma good_mono {P Q : Finset (ℕ × ℕ)} (h : Q ⊆ P) (hP : Good P) : Good Q := by
  intro a b
  rcases hP a b with h1 | h1 | h1
  · exact Or.inl (fun hq => h1 (h hq))
  · exact Or.inr (Or.inl (fun hq => h1 (h hq)))
  · exact Or.inr (Or.inr (fun hq => h1 (h hq)))

def g (k : ℕ) : ℕ := ((G k).powerset.filter Good).sup card

lemma le_g {k : ℕ} {P : Finset (ℕ × ℕ)} (h : P ⊆ G k) (hP : Good P) : P.card ≤ g k :=
  le_sup (f := card) (mem_filter.2 ⟨mem_powerset.2 h, hP⟩)

lemma exists_g (k : ℕ) : ∃ P, P ⊆ G k ∧ Good P ∧ P.card = g k := by
  have hne : ((G k).powerset.filter Good).Nonempty :=
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, fun a b => Or.inl (by simp)⟩⟩
  obtain ⟨P, hP, h⟩ := exists_mem_eq_sup _ hne card
  rw [mem_filter, mem_powerset] at hP
  exact ⟨P, hP.1, hP.2, h.symm⟩

lemma g_le_card (k : ℕ) : g k ≤ (G k).card :=
  Finset.sup_le (fun _P hP => card_le_card (mem_powerset.1 (mem_filter.1 hP).1))

lemma g_zero : g 0 = 0 := by
  have : G 0 = ∅ := by
    ext p
    simp only [mem_G, Finset.notMem_empty, iff_false, not_le]
    positivity
  have := g_le_card 0
  simp_all

lemma g_mono {j k : ℕ} (h : j ≤ k) : g j ≤ g k := by
  obtain ⟨P, hP, hg, hc⟩ := exists_g j
  rw [← hc]
  exact le_g (fun p hp => mem_G.2 (le_trans (mem_G.1 (hP hp)) h)) hg

def d (j : ℕ) : ℕ := g j - g (j - 1)

lemma g_tele (k : ℕ) : g k = ∑ j ∈ Ioc 0 k, d j := by
  induction k with
  | zero => simp [g_zero]
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih]
    have := g_mono (Nat.le_succ k)
    unfold d
    simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one] at *
    omega

def M (N : ℕ) : Finset ℕ := (Ioc 0 N).filter ok

def c (y : ℕ) : ℕ := (M y).card

def φ (m : ℕ) (p : ℕ × ℕ) : ℕ := m * 2 ^ p.1 * 3 ^ p.2

lemma F_le (N : ℕ) : F N ≤ ∑ m ∈ M N, g (N / m) := by
  refine Finset.sup_le (fun S hS => ?_)
  rw [mem_IntervalNonTernarySets_iff] at hS
  obtain ⟨hT, hS⟩ := hS
  let P : ℕ → Finset (ℕ × ℕ) := fun m => (G (N / m)).filter (fun p => φ m p ∈ S)
  have hsub : S ⊆ (M N).biUnion (fun m => (P m).image (φ m)) := by
    intro n hn
    have hn' := mem_Icc.1 (hS hn)
    obtain ⟨m, a, b, hm, rfl⟩ := exists_dec n (by omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (ok_ne hm)
    have h2 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have h3 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have hmN : m ≤ N := by
      have : m ≤ m * 2 ^ a * 3 ^ b := by
        calc m = m * 1 * 1 := by ring
          _ ≤ m * 2 ^ a * 3 ^ b := by gcongr
      omega
    rw [mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · simp only [M, mem_filter, mem_Ioc]; exact ⟨⟨hm0, hmN⟩, hm⟩
    · rw [mem_image]
      refine ⟨(a, b), ?_, rfl⟩
      simp only [P, mem_filter, mem_G]
      refine ⟨?_, hn⟩
      rw [Nat.le_div_iff_mul_le hm0]
      calc 2 ^ a * 3 ^ b * m = m * 2 ^ a * 3 ^ b := by ring
        _ ≤ N := hn'.2
  have hgood : ∀ m, Good (P m) := by
    intro m a b
    rcases hT (m * 2 ^ a * 3 ^ b) with h | h | h
    · exact Or.inl (fun hp => h (mem_filter.1 hp).2)
    · refine Or.inr (Or.inl (fun hp => h ?_))
      have := (mem_filter.1 hp).2
      simp only [φ] at this
      rw [show 2 * (m * 2 ^ a * 3 ^ b) = m * 2 ^ (a + 1) * 3 ^ b by ring]
      exact this
    · refine Or.inr (Or.inr (fun hp => h ?_))
      have := (mem_filter.1 hp).2
      simp only [φ] at this
      rw [show 3 * (m * 2 ^ a * 3 ^ b) = m * 2 ^ a * 3 ^ (b + 1) by ring]
      exact this
  calc S.card ≤ ((M N).biUnion (fun m => (P m).image (φ m))).card := card_le_card hsub
    _ ≤ ∑ m ∈ M N, ((P m).image (φ m)).card := card_biUnion_le
    _ ≤ ∑ m ∈ M N, (P m).card := sum_le_sum (fun m _ => card_image_le)
    _ ≤ ∑ m ∈ M N, g (N / m) := sum_le_sum (fun m _ => le_g (filter_subset _ _) (hgood m))

lemma F_ge (N : ℕ) : ∑ m ∈ M N, g (N / m) ≤ F N := by
  have hex := fun m => exists_g (N / m)
  choose P hPG hPgood hPcard using hex
  let S := (M N).biUnion (fun m => (P m).image (φ m))
  have memS : ∀ n, n ∈ S → ∃ m, m ∈ M N ∧ ∃ p ∈ P m, φ m p = n := by
    intro n hn
    obtain ⟨m, hm, hn⟩ := mem_biUnion.1 hn
    exact ⟨m, hm, mem_image.1 hn⟩
  have okM : ∀ m ∈ M N, ok m ∧ 0 < m := by
    intro m hm
    simp only [M, mem_filter, mem_Ioc] at hm
    exact ⟨hm.2, hm.1.1⟩
  have hSmem : S ∈ IntervalNonTernarySets N := by
    rw [mem_IntervalNonTernarySets_iff]
    constructor
    · intro n
      by_contra h
      simp only [not_or, not_not] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨m1, hm1, p1, hp1, e1⟩ := memS _ h1
      obtain ⟨m2, hm2, p2, hp2, e2⟩ := memS _ h2
      obtain ⟨m3, hm3, p3, hp3, e3⟩ := memS _ h3
      simp only [φ] at e1 e2 e3
      have u2 := uniq (okM _ hm2).1 (okM _ hm1).1
        (a' := p1.1 + 1) (b' := p1.2) (by rw [e2, ← e1]; ring)
      have u3 := uniq (okM _ hm3).1 (okM _ hm1).1
        (a' := p1.1) (b' := p1.2 + 1) (by rw [e3, ← e1]; ring)
      obtain ⟨r2, a2, b2⟩ := u2
      obtain ⟨r3, a3, b3⟩ := u3
      subst r2; subst r3
      rcases hPgood _ p1.1 p1.2 with k | k | k
      · exact k hp1
      · apply k
        have : p2 = (p1.1 + 1, p1.2) := Prod.ext a2 b2
        rw [← this]; exact hp2
      · apply k
        have : p3 = (p1.1, p1.2 + 1) := Prod.ext a3 b3
        rw [← this]; exact hp3
    · intro n hn
      obtain ⟨m, hm, p, hp, rfl⟩ := memS _ hn
      have hp' := mem_G.1 (hPG m hp)
      obtain ⟨_, hm0⟩ := okM m hm
      rw [Nat.le_div_iff_mul_le hm0] at hp'
      simp only [φ, mem_Icc]
      have h2 : 1 ≤ 2 ^ p.1 := Nat.one_le_pow _ _ (by norm_num)
      have h3 : 1 ≤ 3 ^ p.2 := Nat.one_le_pow _ _ (by norm_num)
      constructor
      · have : 1 ≤ m * 2 ^ p.1 * 3 ^ p.2 := by
          calc 1 = 1 * 1 * 1 := by ring
            _ ≤ m * 2 ^ p.1 * 3 ^ p.2 := by gcongr; exact hm0
        exact this
      · calc m * 2 ^ p.1 * 3 ^ p.2 = 2 ^ p.1 * 3 ^ p.2 * m := by ring
          _ ≤ N := hp'
  have hcard : S.card = ∑ m ∈ M N, g (N / m) := by
    rw [card_biUnion]
    · refine sum_congr rfl (fun m hm => ?_)
      rw [card_image_of_injOn, hPcard]
      intro p _ q _ h
      have := uniq (okM m hm).1 (okM m hm).1 h
      exact Prod.ext this.2.1 this.2.2
    · intro x hx y hy hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n h1 h2
      obtain ⟨p, _, e1⟩ := mem_image.1 h1
      obtain ⟨q, _, e2⟩ := mem_image.1 h2
      simp only [φ] at e1 e2
      exact hxy (uniq (okM x hx).1 (okM y hy).1 (e1.trans e2.symm)).1
  rw [← hcard]
  exact le_sup (f := card) hSmem

lemma F_eq (N : ℕ) : F N = ∑ m ∈ M N, g (N / m) := le_antisymm (F_le N) (F_ge N)

lemma F_formula (N : ℕ) : F N = ∑ j ∈ Ioc 0 N, d j * c (N / j) := by
  rw [F_eq]
  calc ∑ m ∈ M N, g (N / m) = ∑ m ∈ M N, ∑ j ∈ Ioc 0 (N / m), d j :=
        sum_congr rfl (fun m _ => g_tele _)
    _ = ∑ j ∈ Ioc 0 N, ∑ m ∈ M (N / j), d j := by
        apply Finset.sum_comm'
        intro m j
        simp only [M, mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨⟨hm0, hmN⟩, hm⟩, hj0, hjN⟩
          rw [Nat.le_div_iff_mul_le hm0] at hjN
          refine ⟨⟨⟨hm0, ?_⟩, hm⟩, hj0, ?_⟩
          · rw [Nat.le_div_iff_mul_le hj0]; linarith
          · nlinarith
        · rintro ⟨⟨⟨hm0, hmN⟩, hm⟩, hj0, hjN⟩
          rw [Nat.le_div_iff_mul_le hj0] at hmN
          refine ⟨⟨⟨hm0, ?_⟩, hm⟩, hj0, ?_⟩
          · nlinarith
          · rw [Nat.le_div_iff_mul_le hm0]; linarith
    _ = ∑ j ∈ Ioc 0 N, d j * c (N / j) := by
        refine sum_congr rfl (fun j _ => ?_)
        rw [sum_const, smul_eq_mul, mul_comm]
        rfl

lemma c_bounds (y : ℕ) : 3 * c y ≤ y + 3 ∧ y ≤ 3 * c y + 3 := by
  have hA : (Ioc 0 y).card = y := by simp
  have h1 := Finset.card_filter_add_card_filter_not (s := Ioc 0 y) (fun m => 2 ∣ m ∨ 3 ∣ m)
  have h2 : (Ioc 0 y).filter (fun m => 2 ∣ m ∨ 3 ∣ m)
      = (Ioc 0 y).filter (fun m => 2 ∣ m) ∪ (Ioc 0 y).filter (fun m => 3 ∣ m) := filter_or _ _ _
  have h3 : (Ioc 0 y).filter (fun m => 2 ∣ m) ∩ (Ioc 0 y).filter (fun m => 3 ∣ m)
      = (Ioc 0 y).filter (fun m => 6 ∣ m) := by
    rw [← filter_and]; exact filter_congr (fun x _ => by omega)
  have h4 := card_union_add_card_inter ((Ioc 0 y).filter (fun m => 2 ∣ m))
    ((Ioc 0 y).filter (fun m => 3 ∣ m))
  have h5 : c y = ((Ioc 0 y).filter (fun m => ¬(2 ∣ m ∨ 3 ∣ m))).card := by
    unfold c M; congr 1; exact filter_congr (fun x _ => by simp [ok, not_or])
  rw [h3, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at h4
  rw [h2] at h1
  omega

lemma c_le (y : ℕ) : c y ≤ y := (card_filter_le _ _).trans (by simp)

lemma d_le_one (j : ℕ) : d j ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [d]
  obtain ⟨P, hP, hg, hc⟩ := exists_g j
  have hQ : (P.filter (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2 ≤ j - 1)).card ≤ g (j - 1) :=
    le_g (fun p hp => mem_G.2 (mem_filter.1 hp).2) (good_mono (filter_subset _ _) hg)
  have hR : (P.filter (fun p : ℕ × ℕ => ¬ 2 ^ p.1 * 3 ^ p.2 ≤ j - 1)).card ≤ 1 := by
    rw [card_le_one]
    intro p hp q hq
    have hp1 := mem_G.1 (hP (mem_filter.1 hp).1)
    have hp2 := (mem_filter.1 hp).2
    have hq1 := mem_G.1 (hP (mem_filter.1 hq).1)
    have hq2 := (mem_filter.1 hq).2
    have e1 : 2 ^ p.1 * 3 ^ p.2 = j := by
      generalize 2 ^ p.1 * 3 ^ p.2 = u at hp1 hp2 ⊢; omega
    have e2 : 2 ^ q.1 * 3 ^ q.2 = j := by
      generalize 2 ^ q.1 * 3 ^ q.2 = u at hq1 hq2 ⊢; omega
    have := uniq1 (e1.trans e2.symm)
    exact Prod.ext this.1 this.2
  have := Finset.card_filter_add_card_filter_not (s := P)
    (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2 ≤ j - 1)
  unfold d
  omega

lemma d_zero_of (j : ℕ) (h : ∀ a b, 2 ^ a * 3 ^ b ≠ j) : d j = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [d]
  have : G j = G (j - 1) := by
    ext p
    rw [mem_G, mem_G]
    have := h p.1 p.2
    generalize 2 ^ p.1 * 3 ^ p.2 = u at this ⊢
    omega
  unfold d g; rw [this]; simp

def e (j : ℕ) : ℝ := (d j : ℝ) / j

lemma e_nonneg (j : ℕ) : 0 ≤ e j := by unfold e; positivity

lemma e_sum (n : ℕ) : ∑ j ∈ range n, e j ≤ 4 := by
  let I := ((range n) ×ˢ (range n)).image (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2)
  have h1 : ∑ j ∈ range n, e j = ∑ j ∈ (range n).filter (· ∈ I), e j := by
    rw [sum_filter_of_ne]
    intro j hj hne
    by_contra hI
    apply hne
    have : d j = 0 := by
      apply d_zero_of
      intro a b hab
      apply hI
      rw [mem_image]
      refine ⟨(a, b), ?_, hab⟩
      have ha : a < 2 ^ a := Nat.lt_pow_self (by norm_num)
      have hb : b < 3 ^ b := Nat.lt_pow_self (by norm_num)
      have h2 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
      have h3 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
      have hjn := mem_range.1 hj
      simp only [mem_product, mem_range]
      constructor <;> nlinarith
    simp [e, this]
  have h2 : ∑ j ∈ (range n).filter (· ∈ I), e j ≤ ∑ j ∈ I, e j :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2) (fun j _ _ => e_nonneg j)
  have h3 : ∑ j ∈ I, e j = ∑ p ∈ (range n) ×ˢ (range n), e (2 ^ p.1 * 3 ^ p.2) := by
    rw [sum_image]
    intro p _ q _ h
    have := uniq1 h
    exact Prod.ext this.1 this.2
  have h4 : ∀ p : ℕ × ℕ, e (2 ^ p.1 * 3 ^ p.2) ≤ (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2 := by
    intro p
    unfold e
    have hd : (d (2 ^ p.1 * 3 ^ p.2) : ℝ) ≤ 1 := by exact_mod_cast d_le_one _
    push_cast
    calc (d (2 ^ p.1 * 3 ^ p.2) : ℝ) / (2 ^ p.1 * 3 ^ p.2) ≤ 1 / (2 ^ p.1 * 3 ^ p.2) := by
          gcongr
      _ ≤ 1 / (2 ^ p.1 * 2 ^ p.2) := by
          apply one_div_le_one_div_of_le (by positivity)
          gcongr; norm_num
      _ = (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2 := by
          rw [one_div_pow, one_div_pow]; field_simp
  calc ∑ j ∈ range n, e j
      ≤ ∑ p ∈ (range n) ×ˢ (range n), (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2 := by
        rw [h1]; refine h2.trans ?_; rw [h3]; exact sum_le_sum (fun p _ => h4 p)
    _ = (∑ a ∈ range n, (1 / 2 : ℝ) ^ a) * (∑ b ∈ range n, (1 / 2 : ℝ) ^ b) := by
        rw [sum_product, sum_mul_sum]
    _ ≤ 4 := by
        have := sum_geometric_two_le n
        have h0 : 0 ≤ ∑ a ∈ range n, (1 / 2 : ℝ) ^ a := sum_nonneg (fun _ _ => by positivity)
        nlinarith

lemma e_summable : Summable e := summable_of_sum_range_le e_nonneg e_sum

def fN (N j : ℕ) : ℝ := if j ∈ Ioc 0 N then (d j : ℝ) * (c (N / j) : ℝ) / N else 0

lemma F_div (N : ℕ) : ∑' j, fN N j = (F N : ℝ) / N := by
  rw [tsum_eq_sum (s := Ioc 0 N) (fun j hj => by simp [fN, hj])]
  have : ∀ j ∈ Ioc 0 N, fN N j = (d j : ℝ) * (c (N / j) : ℝ) / N :=
    fun j hj => by simp only [fN, if_pos hj]
  rw [sum_congr rfl this, F_formula, Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul, Nat.cast_mul]

lemma ratio (j : ℕ) (hj : 0 < j) :
    Tendsto (fun N : ℕ => (c (N / j) : ℝ) / N) atTop (𝓝 (1 / (3 * j))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat 2)
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨h1, h2⟩ := c_bounds (N / j)
  have h3 := Nat.div_add_mod N j
  have h4 := Nat.mod_lt N hj
  set q := N / j
  set r := N % j
  set cc := c q
  have R1 : (3 * cc : ℝ) ≤ q + 3 := by exact_mod_cast h1
  have R2 : (q : ℝ) ≤ 3 * cc + 3 := by exact_mod_cast h2
  have R3 : (j * q + r : ℝ) = N := by exact_mod_cast h3
  have R4 : (r : ℝ) < j := by exact_mod_cast h4
  have R5 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have key : (cc : ℝ) / N - 1 / (3 * j) = (3 * j * cc - N) / (3 * j * N) := by
    field_simp
  have P1 := mul_le_mul_of_nonneg_left R1 (by linarith : (0 : ℝ) ≤ j)
  have P2 := mul_le_mul_of_nonneg_left R2 (by linarith : (0 : ℝ) ≤ j)
  have hX : |(3 * j * cc - N : ℝ)| ≤ 4 * j := by
    rw [abs_le]; constructor <;> nlinarith
  have P3 := mul_le_mul_of_nonneg_right hX (by linarith : (0 : ℝ) ≤ N)
  rw [Real.norm_eq_abs, key, abs_div, abs_of_pos (show (0 : ℝ) < 3 * j * N by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma pointwise (j : ℕ) : Tendsto (fun N => fN N j) atTop (𝓝 ((d j : ℝ) / (3 * j))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [fN]
  · have h := (ratio j hj).const_mul (d j : ℝ)
    have e' : (d j : ℝ) * (1 / (3 * j)) = (d j : ℝ) / (3 * j) := by ring
    rw [e'] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    have : j ∈ Ioc 0 N := mem_Ioc.2 ⟨hj, hN⟩
    simp only [fN, if_pos this]
    ring

lemma bound (N j : ℕ) : ‖fN N j‖ ≤ e j := by
  unfold fN
  split_ifs with h
  · have hj := (mem_Ioc.1 h).1
    have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hj (mem_Ioc.1 h).2
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have hc : (c (N / j) : ℝ) ≤ (N : ℝ) / j :=
      le_trans (by exact_mod_cast c_le (N / j)) Nat.cast_div_le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold e
    calc (d j : ℝ) * c (N / j) / N ≤ d j * ((N : ℝ) / j) / N := by gcongr
      _ = d j / j := by field_simp
  · simpa using e_nonneg j

end

end GS

theorem erdos_168.variants.limit_exists :
    ∃ x, Filter.Tendsto (fun N => (F N / N : ℝ)) Filter.atTop (𝓝 x) := by
  refine ⟨∑' j, (GS.d j : ℝ) / (3 * j), ?_⟩
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := GS.fN)
    (g := fun j => (GS.d j : ℝ) / (3 * j)) GS.e_summable GS.pointwise
    (Eventually.of_forall (fun N j => GS.bound N j))
  exact h.congr GS.F_div

#print axioms erdos_168.variants.limit_exists

end Erdos168
