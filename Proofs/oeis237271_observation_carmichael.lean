import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Data.ZMod.Basic

/-- Restated from FormalConjecturesForMathlib/NumberTheory/Carmichael.lean. -/
def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

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

lemma two_le_countP {α : Type*} (P : α → Bool) (Z : List α) (m : ℕ) (h0 : 0 < m)
    (hm : m < Z.length) (hP0 : P (Z[0]'(by omega)) = true) (hPm : P Z[m] = true) :
    2 ≤ Z.countP P := by
  cases Z with
  | nil => simp at hm
  | cons x Z' =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : m' < Z'.length := by simp at hm; omega
    have h1 : 0 < Z'.countP P :=
      List.countP_pos_iff.mpr ⟨Z'[m'], List.getElem_mem hm', by simpa using hPm⟩
    rw [List.countP_cons]
    simp only [List.getElem_cons_zero] at hP0
    simp only [hP0, ↓reduceIte]
    omega

lemma odd_of_carmichael (k : ℕ) (hk : IsCarmichael k) : Odd k ∧ ¬ k.Prime ∧ 1 < k := by
  obtain ⟨-, hnp, hk1⟩ := hk 1 le_rfl (Nat.coprime_one_right k)
  refine ⟨?_, hnp, hk1⟩
  by_contra he
  rw [Nat.not_odd_iff_even] at he
  have hk2 : 2 < k := by
    rcases Nat.lt_or_ge 2 k with h | h
    · exact h
    · exfalso
      have : k = 2 := by omega
      exact hnp (this ▸ Nat.prime_two)
  have hcop : k.Coprime (k - 1) := by
    have := (Nat.coprime_add_self_left (m := 1) (n := k - 1)).mpr (Nat.coprime_one_left _)
    rwa [show 1 + (k - 1) = k by omega] at this
  obtain ⟨hpp, -, -⟩ := hk (k - 1) (by omega) hcop
  have hx : 1 ≤ (k - 1) ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hmod : 1 ≡ (k - 1) ^ (k - 1) [MOD k] := (Nat.modEq_iff_dvd' hx).mpr hpp
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  have hodd1 : Odd (k - 1) := Nat.Even.sub_odd (by omega) he odd_one
  rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ k), ZMod.natCast_self, Nat.cast_one,
    zero_sub, hodd1.neg_one_pow] at hz
  have h2 : ((2 : ℕ) : ZMod k) = 0 := by
    rw [Nat.cast_ofNat, ← one_add_one_eq_two]
    nth_rewrite 1 [hz]
    exact neg_add_cancel 1
  have hd : k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 k).mp h2
  have := Nat.le_of_dvd (by decide) hd
  omega

theorem observation_carmichael (k : ℕ) (hk : IsCarmichael k) :
    3 ≤ a k := by
  obtain ⟨hodd, hnp, hk1⟩ := odd_of_carmichael k hk
  unfold a
  simp only
  set D := k.divisors.sort (· ≤ ·) with hD
  have hk0 : 0 < k := by omega
  have memD : ∀ x, x ∈ D ↔ x ∣ k := fun x => by
    rw [hD, Finset.mem_sort, Nat.mem_divisors]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have hpw : D.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnd : D.Nodup := Finset.sort_nodup _ _
  have hle : ∀ i j (hi : i < D.length) (hj : j < D.length), i ≤ j → D[i] ≤ D[j] := by
    intro i j hi hj hij
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hpw i j hi hj h
  have hlt : ∀ i j (hi : i < D.length) (hj : j < D.length), i < j → D[i] < D[j] := by
    intro i j hi hj hij
    refine lt_of_le_of_ne (hle i j hi hj hij.le) ?_
    intro heq
    have := (List.Nodup.getElem_inj_iff hnd).mp heq
    omega
  have hdvd : ∀ i (hi : i < D.length), D[i] ∣ k := fun i hi =>
    (memD _).mp (List.getElem_mem hi)
  -- length ≥ 3
  have hlen : 3 ≤ D.length := by
    rw [hD, Finset.length_sort]
    have hp1 : 1 < k.minFac := (Nat.minFac_prime (by omega)).one_lt
    have hpk : k.minFac < k := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
    have h3 : ({1, k.minFac, k} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr ⟨1, k.minFac, k, by omega, by omega, by omega, rfl⟩
    rw [← h3]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    rcases hx with rfl | rfl | rfl
    · exact ⟨one_dvd _, by omega⟩
    · exact ⟨Nat.minFac_dvd _, by omega⟩
    · exact ⟨dvd_rfl, by omega⟩
  -- first element is 1
  have hfirst : D[0]'(by omega) = 1 := by
    obtain ⟨j, hj, hj1⟩ := List.mem_iff_getElem.mp ((memD 1).mpr (one_dvd k))
    have h1 := hle 0 j (by omega) hj (Nat.zero_le _)
    have h2 : 0 < D[0]'(by omega) := Nat.pos_of_dvd_of_pos (hdvd 0 (by omega)) hk0
    omega
  -- last element is k
  have hlast : D[D.length - 2 + 1]'(by omega) = k := by
    obtain ⟨j, hj, hjk⟩ := List.mem_iff_getElem.mp ((memD k).mpr dvd_rfl)
    have h1 := hle j (D.length - 2 + 1) hj (by omega) (by omega)
    have h2 := Nat.le_of_dvd hk0 (hdvd (D.length - 2 + 1) (by omega))
    omega
  have hoddD : ∀ i (hi : i < D.length), Odd D[i] := fun i hi =>
    Odd.of_dvd_nat hodd (hdvd i hi)
  have key := two_le_countP
    (fun pair : ℕ × ℕ => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1)) (D.zip D.tail)
    (D.length - 2) (by omega) (by simp; omega) ?_ ?_
  · omega
  · simp only [List.getElem_zip, List.getElem_tail, decide_eq_true_eq]
    refine ⟨hoddD _ _, ?_⟩
    have := hlt 0 (0 + 1) (by omega) (by omega) (by omega)
    omega
  · simp only [List.getElem_zip, List.getElem_tail, decide_eq_true_eq]
    refine ⟨hoddD _ _, ?_⟩
    have hl := hlt (D.length - 2) (D.length - 2 + 1) (by omega) (by omega) (by omega)
    rw [hlast] at hl ⊢
    obtain ⟨m, hm⟩ := hdvd (D.length - 2) (by omega)
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · interval_cases m <;> omega
      · exact h
    calc 2 * D[D.length - 2] = D[D.length - 2] * 2 := Nat.mul_comm _ _
      _ ≤ D[D.length - 2] * m := Nat.mul_le_mul_left _ hm2
      _ = k := hm.symm

#print axioms observation_carmichael

end OeisA237271
