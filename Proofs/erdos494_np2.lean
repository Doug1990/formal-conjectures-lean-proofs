import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

namespace NP2

lemma S_insert {y : ℂ} {s : Finset ℂ}
    (h : y ∉ s) : sumMultiset (insert y s) 2 = sumMultiset s 2 + s.val.map (fun x => y + x) := by
  unfold sumMultiset
  have e := Finset.powersetCard_succ_insert h 1
  have hd : Disjoint (s.powersetCard (Nat.succ 1)) ((s.powersetCard 1).image (insert y)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    have h1 := (Finset.mem_powersetCard.mp ht).1
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht'
    exact h (h1 (Finset.mem_insert_self y u))
  rw [← Finset.disjUnion_eq_union _ _ hd] at e
  have e2 : (2 : ℕ) = Nat.succ 1 := rfl
  rw [e2, e, Finset.disjUnion_val, Multiset.map_add]
  congr 1
  have hinj : Set.InjOn (insert y) (↑(s.powersetCard 1) : Set (Finset ℂ)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.powersetCard_one] at ha hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    have hab' : insert y ({a'} : Finset ℂ) = insert y ({b'} : Finset ℂ) := hab
    have hm : a' ∈ insert y ({b'} : Finset ℂ) := by
      rw [← hab']
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact absurd (hm ▸ ha') h
    · simp [hm]
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map, Finset.powersetCard_one,
    Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x hx => ?_)
  have hxy : y ≠ x := fun hh => h (hh ▸ Finset.mem_val.mp hx)
  simp only [Function.comp, Function.Embedding.coeFn_mk]
  rw [Finset.sum_insert (by simpa using hxy), Finset.sum_singleton]
  rfl

/-- Power sum of the 2-sums. -/
noncomputable def Q (m : ℕ) (A : Finset ℂ) : ℂ := ((sumMultiset A 2).map (fun z => z ^ m)).sum

/-- Power sum. -/
noncomputable def P (m : ℕ) (A : Finset ℂ) : ℂ := ∑ a ∈ A, a ^ m

lemma Q_eq (m : ℕ) (A : Finset ℂ) :
    2 * Q m A + 2 ^ m * P m A = ∑ a ∈ A, ∑ b ∈ A, (a + b) ^ m := by
  induction A using Finset.induction_on with
  | empty =>
    have h0 : (∅ : Finset ℂ).powersetCard 2 = ∅ := Finset.powersetCard_eq_empty.mpr (by simp)
    simp [Q, P, sumMultiset, h0]
  | insert y s hy ih =>
    have hQ : Q m (insert y s) = Q m s + ∑ x ∈ s, (y + x) ^ m := by
      unfold Q
      rw [S_insert hy, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
      rfl
    have hP : P m (insert y s) = y ^ m + P m s := by
      unfold P
      rw [Finset.sum_insert hy]
    rw [hQ, hP, Finset.sum_insert hy, Finset.sum_insert hy,
      Finset.sum_congr rfl (fun a _ => Finset.sum_insert hy), Finset.sum_add_distrib]
    have hc : ∑ a ∈ s, (a + y) ^ m = ∑ x ∈ s, (y + x) ^ m :=
      Finset.sum_congr rfl (fun a _ => by rw [add_comm])
    rw [hc, ← two_mul, mul_pow]
    linear_combination ih

lemma T_eq (m : ℕ) (A : Finset ℂ) :
    ∑ a ∈ A, ∑ b ∈ A, (a + b) ^ m =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) * (P j A * P (m - j) A) := by
  calc ∑ a ∈ A, ∑ b ∈ A, (a + b) ^ m
      = ∑ a ∈ A, ∑ b ∈ A, ∑ j ∈ Finset.range (m + 1), a ^ j * b ^ (m - j) * (m.choose j : ℂ) := by
        simp_rw [add_pow]
    _ = ∑ a ∈ A, ∑ j ∈ Finset.range (m + 1), ∑ b ∈ A, a ^ j * b ^ (m - j) * (m.choose j : ℂ) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ j ∈ Finset.range (m + 1), ∑ a ∈ A, ∑ b ∈ A, a ^ j * b ^ (m - j) * (m.choose j : ℂ) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        unfold P
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring

lemma P_zero (A : Finset ℂ) : P 0 A = A.card := by
  simp [P]

/-- Equal 2-sums and a non-power-of-two cardinality give equal power sums. -/
lemma P_eq (n : ℕ) (hn : ∀ l : ℕ, n ≠ 2 ^ l) (A B : Finset ℂ) (hA : A.card = n)
    (hB : B.card = n) (hS : sumMultiset A 2 = sumMultiset B 2) : ∀ m, P m A = P m B := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | k
    · rw [P_zero, P_zero, hA, hB]
    · have hQ : Q (k + 1) A = Q (k + 1) B := by unfold Q; rw [hS]
      have hA' := Q_eq (k + 1) A
      have hB' := Q_eq (k + 1) B
      rw [T_eq, Finset.sum_range_succ, Finset.sum_range_succ'] at hA' hB'
      have hmid : ∑ j ∈ Finset.range k, ((k + 1).choose (j + 1) : ℂ) *
            (P (j + 1) A * P (k + 1 - (j + 1)) A) =
          ∑ j ∈ Finset.range k, ((k + 1).choose (j + 1) : ℂ) *
            (P (j + 1) B * P (k + 1 - (j + 1)) B) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        rw [ih (j + 1) (by omega), ih (k + 1 - (j + 1)) (by omega)]
      rw [hmid] at hA'
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
        Nat.sub_self, P_zero, hA, hB] at hA' hB'
      have key : ((2 * n : ℂ) - 2 ^ (k + 1)) * (P (k + 1) A - P (k + 1) B) = 0 := by
        linear_combination hB' - hA' + 2 * hQ
      have hne : (2 * n : ℂ) - 2 ^ (k + 1) ≠ 0 := by
        intro h0
        have h1 : ((2 * n : ℕ) : ℂ) = ((2 ^ (k + 1) : ℕ) : ℂ) := by
          push_cast
          linear_combination h0
        have h2 : 2 * n = 2 ^ (k + 1) := by exact_mod_cast h1
        exact hn k (by rw [pow_succ] at h2; omega)
      have := (mul_eq_zero.mp key).resolve_left hne
      linear_combination this

open Polynomial in
lemma sum_eval (r : ℂ[X]) (A : Finset ℂ) :
    ∑ a ∈ A, r.eval a = ∑ i ∈ Finset.range (r.natDegree + 1), r.coeff i * P i A := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold P
  rw [Finset.mul_sum]

open Polynomial in
/-- Equal power sums force inclusion. -/
lemma subset_of_P (A B : Finset ℂ) (h : ∀ m, P m A = P m B) : A ⊆ B := by
  intro a₀ ha₀
  by_contra hb
  let r : ℂ[X] := (∏ a ∈ A.erase a₀, (X - C a)) * ∏ b ∈ B, (X - C b)
  have hsum : ∑ a ∈ A, r.eval a = ∑ b ∈ B, r.eval b := by
    rw [sum_eval, sum_eval]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h i]
  have hB0 : ∑ b ∈ B, r.eval b = 0 := by
    refine Finset.sum_eq_zero (fun b hb' => ?_)
    simp only [r, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero hb' (sub_self b), mul_zero]
  have hA0 : ∑ a ∈ A, r.eval a = r.eval a₀ := by
    refine Finset.sum_eq_single a₀ (fun a ha hne => ?_) (fun h' => absurd ha₀ h')
    simp only [r, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, ha⟩) (sub_self a), zero_mul]
  have hne : r.eval a₀ ≠ 0 := by
    simp only [r, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    refine mul_ne_zero ?_ ?_
    · rw [Finset.prod_ne_zero_iff]
      intro a ha
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm
    · rw [Finset.prod_ne_zero_iff]
      intro b hb'
      exact sub_ne_zero.mpr (fun e => hb (e ▸ hb'))
  exact hne (hA0 ▸ hsum ▸ hB0)

end NP2

theorem erdos_494.variants.k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  intro card hc A B hA hB hS
  have hP := NP2.P_eq card hc A B hA hB hS
  exact Finset.eq_of_subset_of_card_le (NP2.subset_of_P A B hP) (by rw [hA, hB])

end Erdos494

#print axioms Erdos494.erdos_494.variants.k_eq_2_card_not_pow_two
