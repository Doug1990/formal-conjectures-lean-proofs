import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Filter Asymptotics Finset

/-- Restated from FormalConjecturesForMathlib/Geometry/Metric.lean. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- Restated from FormalConjecturesForMathlib/Geometry/Metric.lean. -/
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

namespace Erdos1087

def HasRepeatedDistance (S : Finset ℝ²) : Prop :=
  distinctDistances S < S.card.choose 2

open scoped Classical in
noncomputable def degenerateCount (P : Finset ℝ²) : ℕ :=
  ((P.powersetCard 4).filter HasRepeatedDistance).card

noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m}

namespace UP

open scoped Classical

/-- Two circles with distinct centres meet in at most two points. -/
lemma circ (P : Finset ℝ²) {a a' : ℝ²} (h : a ≠ a') (r r' : ℝ) :
    #(P.filter fun x => dist x a = r ∧ dist x a' = r') ≤ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨p1, hp1, p2, hp2, p3, hp3, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter] at hp1 hp2 hp3
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (finrank_euclideanSpace_fin) h h12 hp1.2.1 hp2.2.1 hp3.2.1 hp1.2.2 hp2.2.2 hp3.2.2 with e | e
  · exact h13 e.symm
  · exact h23 e.symm

/-- Cauchy–Schwarz double counting with bounded codegrees. -/
lemma cs {α β : Type*} [DecidableEq α] (U : Finset β) (V : Finset α) (R : β → α → Prop)
    [∀ u a, Decidable (R u a)] (c : ℕ)
    (hc : ∀ a ∈ V, ∀ a' ∈ V, a ≠ a' → #(U.filter fun u => R u a ∧ R u a') ≤ c) :
    (∑ u ∈ U, #(V.filter (R u))) ^ 2 ≤
      #U * ((∑ u ∈ U, #(V.filter (R u))) + #V * (c * #V)) := by
  refine (sq_sum_le_card_mul_sum_sq).trans (Nat.mul_le_mul_left _ ?_)
  have e1 : ∀ u ∈ U, #(V.filter (R u)) ^ 2 =
      ∑ a ∈ V, ∑ a' ∈ V, (if R u a ∧ R u a' then 1 else 0) := by
    intro u _
    rw [Finset.card_filter, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
    by_cases h1 : R u a <;> by_cases h2 : R u a' <;> simp [h1, h2]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ a ∈ V, ∑ u ∈ U, ∑ a' ∈ V, (if R u a ∧ R u a' then 1 else 0) =
      ∑ a' ∈ V, #(U.filter fun u => R u a ∧ R u a') := by
    intro a _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a' _ => (Finset.card_filter _ _).symm)
  rw [Finset.sum_congr rfl e2]
  have e3 : ∀ a ∈ V, ∑ a' ∈ V, #(U.filter fun u => R u a ∧ R u a') ≤
      #(U.filter fun u => R u a) + c * #V := by
    intro a ha
    rw [← Finset.add_sum_erase V _ ha]
    have : #(U.filter fun u => R u a ∧ R u a) = #(U.filter fun u => R u a) := by simp
    rw [this]
    refine Nat.add_le_add_left ?_ _
    calc ∑ a' ∈ V.erase a, #(U.filter fun u => R u a ∧ R u a') ≤ ∑ a' ∈ V.erase a, c :=
          Finset.sum_le_sum (fun a' ha' => hc a ha a' (Finset.mem_of_mem_erase ha')
            (Finset.ne_of_mem_erase ha').symm)
      _ ≤ c * #V := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ Finset.card_erase_le
  calc _ ≤ ∑ a ∈ V, (#(U.filter fun u => R u a) + c * #V) := Finset.sum_le_sum e3
    _ = (∑ u ∈ U, #(V.filter (R u))) + #V * (c * #V) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      congr 1
      simp only [Finset.card_filter]
      exact Finset.sum_comm

/-- Ordered pairs at distance r. -/
noncomputable def E (P : Finset ℝ²) (r : ℝ) : Finset (ℝ² × ℝ²) :=
  (P ×ˢ P).filter (fun q => q.1 ≠ q.2 ∧ dist q.1 q.2 = r)

lemma E_sum (P : Finset ℝ²) (r : ℝ) :
    #(E P r) = ∑ x ∈ P, #(P.filter (fun y => x ≠ y ∧ dist x y = r)) := by
  unfold E
  rw [Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)

lemma E_sq (P : Finset ℝ²) (r : ℝ) : #(E P r) ^ 2 ≤ 3 * #P ^ 3 := by
  have hle : #(E P r) ≤ #P * #P := by
    unfold E; exact (Finset.card_filter_le _ _).trans (Finset.card_product _ _).le
  have h := cs P P (fun x y => x ≠ y ∧ dist x y = r) 2 (by
    intro y _ y' _ hyy'
    refine le_trans (Finset.card_le_card ?_) (circ P hyy' r r)
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1.2, hx.2.2.2⟩)
  rw [← E_sum] at h
  calc #(E P r) ^ 2 ≤ #P * (#(E P r) + #P * (2 * #P)) := h
    _ ≤ #P * (#P * #P + #P * (2 * #P)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hle _)
    _ = 3 * #P ^ 3 := by ring

/-- Isosceles triples (apex, b, c). -/
noncomputable def Tri (P : Finset ℝ²) : Finset (ℝ² × (ℝ² × ℝ²)) :=
  (P ×ˢ (P ×ˢ P)).filter (fun t => t.2.1 ≠ t.2.2 ∧ dist t.1 t.2.1 = dist t.1 t.2.2)

lemma Tri_sum (P : Finset ℝ²) :
    #(Tri P) = ∑ u ∈ P ×ˢ P, #(P.filter (fun a => u.1 ≠ u.2 ∧ dist a u.1 = dist a u.2)) := by
  unfold Tri
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ => (Finset.card_filter _ _).symm)

lemma Tri_sq (P : Finset ℝ²) : #(Tri P) ^ 2 ≤ 3 * #P ^ 5 := by
  have hle : #(Tri P) ≤ #P * (#P * #P) := by
    unfold Tri
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Finset.card_product]
  have h := cs (P ×ˢ P) P (fun u a => u.1 ≠ u.2 ∧ dist a u.1 = dist a u.2) (2 * #P) (by
    intro a _ a' _ haa'
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ b ∈ P, ∑ c ∈ P, (if ((b, c).1 ≠ (b, c).2 ∧ dist a (b, c).1 = dist a (b, c).2) ∧
            ((b, c).1 ≠ (b, c).2 ∧ dist a' (b, c).1 = dist a' (b, c).2) then 1 else 0)
          ≤ ∑ b ∈ P, 2 := by
            refine Finset.sum_le_sum (fun b _ => ?_)
            rw [← Finset.card_filter]
            refine le_trans (Finset.card_le_card ?_) (circ P haa' (dist a b) (dist a' b))
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, ?_, ?_⟩
            · rw [dist_comm]; exact hx.2.1.2.symm
            · rw [dist_comm]; exact hx.2.2.2.symm
      _ = 2 * #P := by rw [Finset.sum_const, smul_eq_mul, mul_comm])
  rw [← Tri_sum, Finset.card_product] at h
  calc #(Tri P) ^ 2 ≤ #P * #P * (#(Tri P) + #P * (2 * #P * #P)) := h
    _ ≤ #P * #P * (#P * (#P * #P) + #P * (2 * #P * #P)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hle _)
    _ = 3 * #P ^ 5 := by ring

/-- A degenerate 4-set has two different unordered pairs at the same distance. -/
lemma extract (S : Finset ℝ²) (hS : #S = 4) (h : HasRepeatedDistance S) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, ∃ w ∈ S, x ≠ y ∧ z ≠ w ∧ dist x y = dist z w ∧
      ¬(x = z ∧ y = w) ∧ ¬(x = w ∧ y = z) := by
  by_contra hno
  unfold HasRepeatedDistance distinctDistances distanceSet at h
  have hfib : ∀ d ∈ S.offDiag.image (fun p : ℝ² × ℝ² => dist p.1 p.2),
      #(S.offDiag.filter fun p => dist p.1 p.2 = d) ≤ 2 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_offDiag] at hp
    refine le_trans (Finset.card_le_card (t := ({p, p.swap} : Finset (ℝ² × ℝ²))) ?_)
      Finset.card_le_two
    intro q hq
    rw [Finset.mem_filter, Finset.mem_offDiag] at hq
    by_contra hq'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
    refine hno ⟨q.1, hq.1.1, q.2, hq.1.2.1, p.1, hp.1, p.2, hp.2.1, hq.1.2.2, hp.2.2, hq.2,
      ?_, ?_⟩
    · rintro ⟨e1, e2⟩; exact hq'.1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact hq'.2 (Prod.ext e1 e2)
  have := Finset.card_le_mul_card_image S.offDiag 2 hfib
  rw [Finset.offDiag_card, hS] at this
  rw [hS] at h
  have h6 : Nat.choose 4 2 = 6 := rfl
  omega

lemma card4 {a b c d : ℝ²} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) : #({a, b, c, d} : Finset ℝ²) = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
    Finset.card_insert_of_notMem (by simp [h4, h5]), Finset.card_pair h6]

noncomputable def QA (P : Finset ℝ²) : Finset ((ℝ² × ℝ²) × (ℝ² × ℝ²)) :=
  ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q => q.1.1 ≠ q.1.2 ∧ dist q.1.1 q.1.2 = dist q.2.1 q.2.2)

noncomputable def gA (q : (ℝ² × ℝ²) × (ℝ² × ℝ²)) : Finset ℝ² := {q.1.1, q.1.2, q.2.1, q.2.2}

noncomputable def gB (t : ℝ² × (ℝ² × (ℝ² × ℝ²))) : Finset ℝ² := {t.2.1, t.2.2.1, t.2.2.2, t.1}

lemma QA_sq (P : Finset ℝ²) : #(QA P) ^ 2 ≤ 3 * #P ^ 7 := by
  have hsum : #(QA P) = ∑ v ∈ P ×ˢ P, #(E P (dist v.1 v.2)) := by
    unfold QA
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold E
    rw [Finset.card_filter]
  rw [hsum]
  calc (∑ v ∈ P ×ˢ P, #(E P (dist v.1 v.2))) ^ 2
        ≤ #(P ×ˢ P) * ∑ v ∈ P ×ˢ P, #(E P (dist v.1 v.2)) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ #(P ×ˢ P) * ∑ v ∈ P ×ˢ P, 3 * #P ^ 3 :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun v _ => E_sq P _))
    _ = 3 * #P ^ 7 := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_product]; ring

lemma iso_mem (P S : Finset ℝ²) (hSP : S ⊆ P) (hS : #S = 4) {a b c : ℝ²} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : dist a b = dist a c) : S ∈ (P ×ˢ Tri P).image gB := by
  obtain ⟨e, heS, he⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b, c}) (t := S)
    (by rw [hS]; exact lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  have hsub : ({a, b, c, e} : Finset ℝ²) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : #({a, b, c, e} : Finset ℝ²) = 4 :=
    card4 hab hac (Ne.symm he.1) hbc (Ne.symm he.2.1) (Ne.symm he.2.2)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hS, hcard])
  refine Finset.mem_image.mpr ⟨(e, (a, b, c)), ?_, heq⟩
  simp only [Tri, Finset.mem_product, Finset.mem_filter]
  exact ⟨hSP heS, ⟨hSP ha, hSP hb, hSP hc⟩, hbc, hd⟩

lemma cover (P : Finset ℝ²) : (P.powersetCard 4).filter HasRepeatedDistance ⊆
    (QA P).image gA ∪ (P ×ˢ Tri P).image gB := by
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
  obtain ⟨⟨hSP, hS4⟩, hrep⟩ := hS
  obtain ⟨x, hx, y, hy, z, hz, w, hw, hxy, hzw, hd, hn1, hn2⟩ := extract S hS4 hrep
  rw [Finset.mem_union]
  by_cases hxz : x = z
  · subst hxz
    right; exact iso_mem P S hSP hS4 hx hy hw hxy hzw (fun h => hn1 ⟨rfl, h⟩) hd
  by_cases hxw : x = w
  · subst hxw
    right
    exact iso_mem P S hSP hS4 hx hy hz hxy (Ne.symm hzw) (fun h => hn2 ⟨rfl, h⟩)
      (hd.trans (dist_comm _ _))
  by_cases hyz : y = z
  · subst hyz
    right
    exact iso_mem P S hSP hS4 hy hx hw (Ne.symm hxy) hzw hxw ((dist_comm _ _).trans hd)
  by_cases hyw : y = w
  · subst hyw
    right
    exact iso_mem P S hSP hS4 hy hx hz (Ne.symm hxy) (Ne.symm hzw) hxz
      ((dist_comm _ _).trans (hd.trans (dist_comm _ _)))
  left
  refine Finset.mem_image.mpr ⟨((x, y), (z, w)), ?_, ?_⟩
  · simp only [QA, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hSP hx, hSP hy⟩, hSP hz, hSP hw⟩, hxy, hd⟩
  · refine Finset.eq_of_subset_of_card_le ?_ (by rw [hS4, gA, card4 hxy hxz hxw hyz hyw hzw])
    intro v hv
    simp only [gA, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption

lemma deg_le (P : Finset ℝ²) : degenerateCount P ≤ #(QA P) + #P * #(Tri P) := by
  unfold degenerateCount
  calc _ ≤ #((QA P).image gA ∪ (P ×ˢ Tri P).image gB) := Finset.card_le_card (cover P)
    _ ≤ #((QA P).image gA) + #((P ×ˢ Tri P).image gB) := Finset.card_union_le _ _
    _ ≤ #(QA P) + #(P ×ˢ Tri P) := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by rw [Finset.card_product]

lemma to_real (X m : ℕ) (hX : X ^ 2 ≤ 3 * m ^ 7) : (X : ℝ) ≤ 2 * (m : ℝ) ^ (7 / 2 : ℝ) := by
  have hpow : ((m : ℝ) ^ (7 / 2 : ℝ)) ^ 2 = (m : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      show (7 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : (X : ℝ) ^ 2 ≤ 3 * (m : ℝ) ^ 7 := by exact_mod_cast hX
  have h7 : (0 : ℝ) ≤ (m : ℝ) ^ 7 := by positivity
  have h2 : (X : ℝ) ^ 2 ≤ (2 * (m : ℝ) ^ (7 / 2 : ℝ)) ^ 2 := by
    rw [mul_pow, hpow]; linarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg X) (by positivity) two_ne_zero).mp h2

lemma real_bound (P : Finset ℝ²) :
    (degenerateCount P : ℝ) ≤ 4 * (#P : ℝ) ^ (7 / 2 : ℝ) := by
  have hA := to_real _ _ (QA_sq P)
  have hB : (#P * #(Tri P)) ^ 2 ≤ 3 * #P ^ 7 := by
    calc (#P * #(Tri P)) ^ 2 = #P ^ 2 * #(Tri P) ^ 2 := by ring
      _ ≤ #P ^ 2 * (3 * #P ^ 5) := Nat.mul_le_mul_left _ (Tri_sq P)
      _ = 3 * #P ^ 7 := by ring
  have hB' := to_real _ _ hB
  have hD : (degenerateCount P : ℝ) ≤ (#(QA P) : ℝ) + ((#P * #(Tri P) : ℕ) : ℝ) := by
    exact_mod_cast deg_le P
  linarith

lemma f_le (n : ℕ) : (f n : ℝ) ≤ 4 * (n : ℝ) ^ (7 / 2 : ℝ) := by
  unfold f
  by_cases hne : {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m}.Nonempty
  · have hbdd : BddAbove {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m} := by
      refine ⟨n.choose 4, ?_⟩
      rintro m ⟨P, hP, rfl⟩
      rw [← hP]
      unfold degenerateCount
      exact (Finset.card_filter_le _ _).trans (Finset.card_powersetCard 4 P).le
    obtain ⟨P, hP, hm⟩ := Nat.sSup_mem hne hbdd
    rw [← hm, ← hP]
    exact real_bound P
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty, bot_eq_zero, Nat.cast_zero]
    positivity

end UP

theorem erdos_1087.variants.upper :
    (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (7 / 2 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 4 (Filter.Eventually.of_forall fun n => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity)]
  exact UP.f_le n

end Erdos1087

#print axioms Erdos1087.erdos_1087.variants.upper
