import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring

open Finset

namespace SimpleGraph

/-- Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean). -/
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual

scoped notation "J(" n ", " k ")" => johnson n k

end SimpleGraph

open SimpleGraph

namespace Erdos835

namespace OD

variable {β : Type*} [DecidableEq β] [Fintype β]

/-- Members of a distance-4 family of (r+2)-sets through a fixed r-set have disjoint
two-element remainders. -/
lemma local_bound (r : ℕ) (I : Finset (Finset β)) (hk : ∀ s ∈ I, #s = r + 2)
    (hI : ∀ s ∈ I, ∀ t ∈ I, s ≠ t → #(s ∩ t) ≤ r) (T : Finset β) (hT : #T = r) :
    2 * #(I.filter (fun s => T ⊆ s)) ≤ Fintype.card β - r := by
  have h2 : ∀ s ∈ I.filter (fun s => T ⊆ s), #(s \ T) = 2 := by
    intro s hs
    have hs' := mem_filter.1 hs
    have := card_sdiff_add_card_eq_card hs'.2
    rw [hk s hs'.1, hT] at this
    omega
  have hdisj : ((I.filter (fun s => T ⊆ s) : Finset (Finset β)) : Set (Finset β)).PairwiseDisjoint
      (fun s => s \ T) := by
    intro s hs t ht hst
    have hs' := mem_filter.1 (mem_coe.1 hs)
    have ht' := mem_filter.1 (mem_coe.1 ht)
    have hsub : T ⊆ s ∩ t := subset_inter hs'.2 ht'.2
    have heq : T = s ∩ t :=
      eq_of_subset_of_card_le hsub (by rw [hT]; exact hI s hs'.1 t ht'.1 hst)
    show Disjoint (s \ T) (t \ T)
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_sdiff] at hx hx'
    have hm : x ∈ s ∩ t := mem_inter.2 ⟨hx.1, hx'.1⟩
    rw [← heq] at hm
    exact hx.2 hm
  have hcard := card_biUnion hdisj
  rw [sum_congr rfl h2, sum_const, smul_eq_mul] at hcard
  have hsub : (I.filter (fun s => T ⊆ s)).biUnion (fun s => s \ T) ⊆ univ \ T := by
    intro x hx
    obtain ⟨s, -, hx⟩ := mem_biUnion.1 hx
    exact mem_sdiff.2 ⟨mem_univ x, (mem_sdiff.1 hx).2⟩
  have h3 := card_le_card hsub
  have h4 := card_sdiff_add_card_eq_card (subset_univ T)
  rw [card_univ, hT] at h4
  omega

/-- Double counting of (member, r-subset) incidences. -/
lemma count (r : ℕ) (I : Finset (Finset β)) (hk : ∀ s ∈ I, #s = r + 2) :
    ∑ T ∈ powersetCard r (univ : Finset β), #(I.filter (fun s => T ⊆ s)) =
      #I * (r + 2).choose r := by
  calc ∑ T ∈ powersetCard r (univ : Finset β), #(I.filter (fun s => T ⊆ s))
      = ∑ T ∈ powersetCard r (univ : Finset β), ∑ s ∈ I, (if T ⊆ s then 1 else 0) := by
        refine sum_congr rfl fun T _ => ?_
        rw [sum_boole]; simp
    _ = ∑ s ∈ I, ∑ T ∈ powersetCard r (univ : Finset β), (if T ⊆ s then 1 else 0) := sum_comm
    _ = ∑ s ∈ I, (r + 2).choose r := by
        refine sum_congr rfl fun s hs => ?_
        rw [sum_boole]
        have : (powersetCard r (univ : Finset β)).filter (fun T => T ⊆ s) = powersetCard r s := by
          ext T; simp only [mem_filter, mem_powersetCard, subset_univ, true_and]; tauto
        rw [this, card_powersetCard, hk s hs]; simp
    _ = #I * (r + 2).choose r := by rw [sum_const, smul_eq_mul]

/-- For odd r, an independent set of J(2(r+2), r+2) satisfies
2·|I|·C(r+2,r) ≤ C(2(r+2), r)·(r+3). -/
lemma indep_bound (r : ℕ) (hr : r % 2 = 1) (hβ : Fintype.card β = 2 * (r + 2))
    (I : Finset (Finset β)) (hk : ∀ s ∈ I, #s = r + 2)
    (hI : ∀ s ∈ I, ∀ t ∈ I, s ≠ t → #(s ∩ t) ≤ r) :
    2 * (#I * (r + 2).choose r) ≤ (2 * (r + 2)).choose r * (r + 3) := by
  rw [← count r I hk, mul_sum]
  calc ∑ T ∈ powersetCard r (univ : Finset β), 2 * #(I.filter (fun s => T ⊆ s))
      ≤ ∑ T ∈ powersetCard r (univ : Finset β), (r + 3) := by
        refine sum_le_sum fun T hT => ?_
        have := local_bound r I hk hI T (mem_powersetCard.1 hT).2
        rw [hβ] at this
        omega
    _ = (2 * (r + 2)).choose r * (r + 3) := by
        rw [sum_const, card_powersetCard, card_univ, hβ, smul_eq_mul]

end OD

/--
It can be seen that the chromatic number of $J(2k,k)$ is $>k+1$ for all odd $k>2$.
-/
theorem johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  have hr : r % 2 = 1 := by obtain ⟨m, hm⟩ := h; omega
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨c⟩ : (J(2 * (r + 2), r + 2)).Colorable (r + 3) :=
    chromaticNumber_le_iff_colorable.mp (by exact_mod_cast hcon)
  let I : Fin (r + 3) → Finset (Finset (Fin (2 * (r + 2)))) := fun j =>
    (univ.filter (fun v : {s : Finset (Fin (2 * (r + 2))) // #s = r + 2} => c v = j)).map
      (Function.Embedding.subtype _)
  have hI : ∀ j, 2 * (#(I j) * (r + 2).choose r) ≤ (2 * (r + 2)).choose r * (r + 3) := by
    intro j
    refine OD.indep_bound r hr (by simp) (I j) ?_ ?_
    · intro s hs
      obtain ⟨x, -, rfl⟩ := mem_map.1 hs
      exact x.2
    · intro s hs t ht hst
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hs
      obtain ⟨y, hy, rfl⟩ := mem_map.1 ht
      have hxy : x ≠ y := fun h => hst (by rw [h])
      have hcx := (mem_filter.1 hx).2
      have hcy := (mem_filter.1 hy).2
      have hna : ¬ (J(2 * (r + 2), r + 2)).Adj x y := fun hadj =>
        c.valid hadj (hcx.trans hcy.symm)
      change ¬ (#(x.val ∩ y.val) + 1 = r + 2) at hna
      have hle : #(x.val ∩ y.val) ≤ r + 2 :=
        calc _ ≤ #x.val := card_le_card inter_subset_left
          _ = r + 2 := x.2
      have hlt : #(x.val ∩ y.val) < r + 2 := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso; apply hxy
          have h1 : x.val ∩ y.val = x.val :=
            eq_of_subset_of_card_le inter_subset_left (by rw [h, x.2])
          have h2 : x.val ⊆ y.val := by rw [← h1]; exact inter_subset_right
          exact Subtype.ext (eq_of_subset_of_card_le h2 (by rw [x.2, y.2]))
      simp only [Function.Embedding.coe_subtype]
      omega
  have hsum0 : ∑ j : Fin (r + 3),
      #(univ.filter (fun v : {s : Finset (Fin (2 * (r + 2))) // #s = r + 2} => c v = j)) =
      Fintype.card {s : Finset (Fin (2 * (r + 2))) // #s = r + 2} := by
    rw [← card_univ]
    exact (card_eq_sum_card_fiberwise (f := fun v => c v) (s := univ) (t := univ)
      (fun v _ => mem_coe.2 (mem_univ _))).symm
  have hsum : ∑ j, #(I j) = (2 * (r + 2)).choose (r + 2) := by
    simp only [I, card_map]
    rw [hsum0, Fintype.card_finset_len, Fintype.card_fin]
  have hm := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (r + 3)))) => hI j)
  rw [← mul_sum, ← sum_mul, hsum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hm
  -- binomial identities
  have e1 := Nat.choose_succ_right_eq (2 * (r + 2)) (r + 1)
  rw [show r + 1 + 1 = r + 2 from rfl, show 2 * (r + 2) - (r + 1) = r + 3 by omega] at e1
  have e2 := Nat.choose_succ_right_eq (2 * (r + 2)) r
  rw [show 2 * (r + 2) - r = r + 4 by omega] at e2
  have e3 := Nat.choose_succ_right_eq (r + 2) r
  rw [show r + 2 - r = 2 by omega] at e3
  have hC1 : (r + 2).choose (r + 1) = r + 2 := Nat.choose_succ_self_right (r + 1)
  have hY : 0 < (2 * (r + 2)).choose r := Nat.choose_pos (by omega)
  have k1 : 2 * ((2 * (r + 2)).choose (r + 2) * (r + 2).choose r) =
      ((r + 3) * (2 * (r + 2)).choose r) * (r + 4) := by
    calc 2 * ((2 * (r + 2)).choose (r + 2) * (r + 2).choose r)
        = ((r + 2).choose r * 2) * (2 * (r + 2)).choose (r + 2) := by ring
      _ = ((r + 2).choose (r + 1) * (r + 1)) * (2 * (r + 2)).choose (r + 2) := by rw [← e3]
      _ = (r + 1) * ((2 * (r + 2)).choose (r + 2) * (r + 2)) := by rw [hC1]; ring
      _ = (r + 1) * ((2 * (r + 2)).choose (r + 1) * (r + 3)) := by rw [e1]
      _ = (r + 3) * ((2 * (r + 2)).choose (r + 1) * (r + 1)) := by ring
      _ = (r + 3) * ((2 * (r + 2)).choose r * (r + 4)) := by rw [e2]
      _ = ((r + 3) * (2 * (r + 2)).choose r) * (r + 4) := by ring
  rw [k1] at hm
  have hm2 : ((r + 3) * (2 * (r + 2)).choose r) * (r + 4) ≤
      ((r + 3) * (2 * (r + 2)).choose r) * (r + 3) := by
    calc _ ≤ (r + 3) * ((2 * (r + 2)).choose r * (r + 3)) := hm
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_left hm2 (Nat.mul_pos (by omega) hY)
  omega

end Erdos835

#print axioms Erdos835.johnson_chromaticNumber_odd
