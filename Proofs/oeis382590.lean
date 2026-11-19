import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace OeisA382590

open Int

def abPair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := abPair (n + 1)
  let (a_n, b_n) := abPair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

def a (n : ℕ) : ℤ := (abPair n).fst

open Nat

def kthPrimeFactor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let L := (primeFactorsList n.natAbs).dedup
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

namespace P

/-! ### Sorted lists -/

lemma pw_le (L : List ℕ) (h : L.Pairwise (· < ·)) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) (hij : i ≤ j) : L[i] ≤ L[j] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (List.pairwise_iff_getElem.mp h i j hi hj hlt)

lemma idx_inj (L' : List ℕ) (x y : ℕ) (hx : x ∈ L') (hy : y ∈ L')
    (h : L'.idxOf x = L'.idxOf y) : x = y := by
  have hx' := List.idxOf_lt_length_of_mem hx
  have hy' := List.idxOf_lt_length_of_mem hy
  have e1 : L'[L'.idxOf x]? = some x := by
    rw [List.getElem?_eq_getElem hx', List.getElem_idxOf]
  have e2 : L'[L'.idxOf y]? = some y := by
    rw [List.getElem?_eq_getElem hy', List.getElem_idxOf]
  rw [h, e2] at e1
  exact (Option.some.inj e1).symm

/-- If `L ⊆ L'` are strictly increasing lists, the `i`-th entry of `L'` exists and is at most
the `i`-th entry of `L`. -/
lemma idx_le (L L' : List ℕ) (hL : L.Pairwise (· < ·)) (hL' : L'.Pairwise (· < ·))
    (hsub : ∀ x ∈ L, x ∈ L') (i : ℕ) (hi : i < L.length) :
    ∃ h : i < L'.length, L'[i] ≤ L[i] := by
  by_contra hcon
  have key : ∀ j (hj : j < i + 1), L'.idxOf (L[j]'(by omega)) < i := by
    intro j hj
    have hmem : L[j]'(by omega) ∈ L' := hsub _ (List.getElem_mem ..)
    have hlt := List.idxOf_lt_length_of_mem hmem
    have heq : L'[L'.idxOf (L[j]'(by omega))] = L[j]'(by omega) := List.getElem_idxOf hlt
    by_contra hge
    have hiL' : i < L'.length := by omega
    apply hcon ⟨hiL', ?_⟩
    calc L'[i] ≤ L'[L'.idxOf (L[j]'(by omega))] := pw_le L' hL' hiL' hlt (by omega)
      _ = L[j]'(by omega) := heq
      _ ≤ L[i] := pw_le L hL (by omega) hi (by omega)
  let f : Fin (i + 1) → Fin i := fun j => ⟨L'.idxOf (L[j.1]'(by omega)), key j.1 j.2⟩
  have hf : Function.Injective f := by
    intro j1 j2 h
    have h1 : L'.idxOf (L[j1.1]'(by omega)) = L'.idxOf (L[j2.1]'(by omega)) :=
      congrArg Fin.val h
    have v := idx_inj L' _ _ (hsub _ (List.getElem_mem ..)) (hsub _ (List.getElem_mem ..)) h1
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := List.pairwise_iff_getElem.mp hL j1.1 j2.1 (by omega) (by omega) hlt
      omega
    · have := List.pairwise_iff_getElem.mp hL j2.1 j1.1 (by omega) (by omega) hlt
      omega
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

/-! ### Prime factor lists -/

def PF (z : ℤ) : List ℕ := (primeFactorsList z.natAbs).dedup

lemma pf_pw (z : ℤ) : (PF z).Pairwise (· < ·) := by
  have h1 : (primeFactorsList z.natAbs).Pairwise (· ≤ ·) :=
    List.sortedLE_iff_pairwise.mp (primeFactorsList_sorted _)
  have h2 := h1.sublist (List.dedup_sublist _)
  exact (h2.and (List.nodup_dedup _)).imp (fun h => lt_of_le_of_ne h.1 h.2)

lemma pf_sub (z w : ℤ) (hd : z ∣ w) (hw : w ≠ 0) : ∀ x ∈ PF z, x ∈ PF w := by
  intro x hx
  unfold PF at *
  rw [List.mem_dedup] at hx ⊢
  have hz : z ≠ 0 := by
    rintro rfl
    exact hw (zero_dvd_iff.mp hd)
  rw [Nat.mem_primeFactorsList (Int.natAbs_ne_zero.mpr hz)] at hx
  rw [Nat.mem_primeFactorsList (Int.natAbs_ne_zero.mpr hw)]
  exact ⟨hx.1, hx.2.trans (Int.natAbs_dvd_natAbs.mpr hd)⟩

lemma kth_eq (k : ℕ) (hk : k ≠ 0) (z : ℤ) (h : k - 1 < (PF z).length) :
    kthPrimeFactor k z = (PF z)[k - 1] := by
  unfold PF at h
  simp only [kthPrimeFactor, dif_neg hk]
  rw [dif_neg (by omega)]
  rfl

lemma kth_one (k : ℕ) (hk : k ≠ 0) (z : ℤ) (h : ¬ k - 1 < (PF z).length) :
    kthPrimeFactor k z = 1 := by
  unfold PF at h
  simp only [kthPrimeFactor, dif_neg hk]
  rw [dif_pos (by omega)]

/-! ### Eventually constant -/

lemma anti_stable (u : ℕ → ℕ) (m1 : ℕ) (h : ∀ m ≥ m1, u (m + 1) ≤ u m) :
    ∃ N, ∀ m ≥ N, u (m + 1) = u m := by
  classical
  have hex : ∃ t, ∃ m ≥ m1, u m = t := ⟨u m1, m1, le_refl _, rfl⟩
  obtain ⟨m0, hm0, ht⟩ := Nat.find_spec hex
  have hle : ∀ m ≥ m0, u m ≤ u m0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_refl _
    | succ m hm ih => exact (h m (by omega)).trans ih
  have hge : ∀ m ≥ m1, Nat.find hex ≤ u m := fun m hm => Nat.find_min' hex ⟨m, hm, rfl⟩
  refine ⟨m0, fun m hm => ?_⟩
  have a1 := hle (m + 1) (by omega)
  have a2 := hle m hm
  have b1 := hge (m + 1) (by omega)
  have b2 := hge m (by omega)
  omega

lemma chain (k : ℕ) (hk : k ≠ 0) (c : ℕ → ℤ) (hc : ∀ m, c m ∣ c (m + 1)) :
    ∃ N, ∀ m ≥ N, kthPrimeFactor k (c (m + 1)) = kthPrimeFactor k (c m) := by
  by_cases h0 : ∃ m0, c m0 = 0
  · obtain ⟨m0, hm0⟩ := h0
    have hz : ∀ m ≥ m0, c m = 0 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hm0
      | succ m hm ih =>
        have := hc m
        rw [ih] at this
        exact zero_dvd_iff.mp this
    exact ⟨m0, fun m hm => by rw [hz m hm, hz (m + 1) (by omega)]⟩
  have h0' : ∀ m, c m ≠ 0 := fun m hm => h0 ⟨m, hm⟩
  have hsub : ∀ m, ∀ x ∈ PF (c m), x ∈ PF (c (m + 1)) :=
    fun m => pf_sub _ _ (hc m) (h0' _)
  by_cases hP : ∃ m1, k - 1 < (PF (c m1)).length
  · obtain ⟨m1, hm1⟩ := hP
    have hlen : ∀ m ≥ m1, k - 1 < (PF (c m)).length := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hm1
      | succ m hm ih => exact (idx_le _ _ (pf_pw _) (pf_pw _) (hsub m) _ ih).1
    have hanti : ∀ m ≥ m1, (fun m => kthPrimeFactor k (c m)) (m + 1) ≤
        (fun m => kthPrimeFactor k (c m)) m := by
      intro m hm
      obtain ⟨h1, h2⟩ := idx_le _ _ (pf_pw _) (pf_pw _) (hsub m) _ (hlen m hm)
      show kthPrimeFactor k (c (m + 1)) ≤ kthPrimeFactor k (c m)
      rw [kth_eq k hk _ h1, kth_eq k hk _ (hlen m hm)]
      exact h2
    exact anti_stable (fun m => kthPrimeFactor k (c m)) m1 hanti
  · have hP' : ∀ m, ¬ k - 1 < (PF (c m)).length := fun m hm => hP ⟨m, hm⟩
    exact ⟨0, fun m _ => by rw [kth_one k hk _ (hP' (m + 1)), kth_one k hk _ (hP' m)]⟩

/-! ### The recurrence -/

def bb (n : ℕ) : ℤ := (abPair n).snd

lemma key (m : ℕ) :
    a (m + 4) = a (m + 1) * (2 * (bb m * a (m + 3) - a (m + 2) * bb (m + 2))) := by
  have e4 : a (m + 4) = a (m + 3) * bb (m + 2) + a (m + 2) * bb (m + 3) := rfl
  have f3 : bb (m + 3) = a (m + 2) * bb (m + 1) - a (m + 1) * bb (m + 2) := rfl
  have e3 : a (m + 3) = a (m + 2) * bb (m + 1) + a (m + 1) * bb (m + 2) := rfl
  have f2 : bb (m + 2) = a (m + 1) * bb m - a m * bb (m + 1) := rfl
  have e2 : a (m + 2) = a (m + 1) * bb m + a m * bb (m + 1) := rfl
  rw [e4, f3, e3, f2, e2]
  ring

lemma dvd3 (n : ℕ) : a n ∣ a (n + 3) := by
  rcases n with _ | m
  · show a 0 ∣ _
    rw [show a 0 = 1 from rfl]
    exact one_dvd _
  · exact ⟨_, key m⟩

end P

theorem kthPrimeFactor_periodic : ∀ k : ℕ, k ≥ 2 → ∃ N₀ p : ℕ, p > 0 ∧
    ∀ n : ℕ, n ≥ N₀ → kthPrimeFactor k (a (n + p)) = kthPrimeFactor k (a n) := by
  intro k hk
  have hk0 : k ≠ 0 := by omega
  have hr : ∀ r, ∃ N, ∀ m ≥ N,
      kthPrimeFactor k (a (r + 3 * (m + 1))) = kthPrimeFactor k (a (r + 3 * m)) := by
    intro r
    exact P.chain k hk0 (fun m => a (r + 3 * m)) (fun m => by
      have := P.dvd3 (r + 3 * m)
      rwa [show r + 3 * m + 3 = r + 3 * (m + 1) by omega] at this)
  obtain ⟨N0, h0⟩ := hr 0
  obtain ⟨N1, h1⟩ := hr 1
  obtain ⟨N2, h2⟩ := hr 2
  refine ⟨3 * (N0 + N1 + N2), 3, by omega, fun n hn => ?_⟩
  obtain ⟨r, q, hr3, rfl⟩ : ∃ r q, r < 3 ∧ n = r + 3 * q := ⟨n % 3, n / 3, by omega, by omega⟩
  rw [show r + 3 * q + 3 = r + 3 * (q + 1) by omega]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · exact h0 q (by omega)
  · exact h1 q (by omega)
  · exact h2 q (by omega)

end OeisA382590

#print axioms OeisA382590.kthPrimeFactor_periodic
