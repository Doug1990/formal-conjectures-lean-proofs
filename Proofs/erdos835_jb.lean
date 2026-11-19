import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

open Finset

namespace SimpleGraph

/-- Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean). -/
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual

scoped notation "J(" n ", " k ")" => johnson n k

/-- Restated from the checkout (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean). -/
scoped notation "α(" G ")" => indepNum G

end SimpleGraph

open SimpleGraph

namespace Erdos835

variable {n k : ℕ}

/-- Restated from the checkout (ErdosProblems/835.lean). -/
def johnsonBound : ℕ → ℕ → ℕ → ℕ
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)

namespace JB

variable {β : Type*} [DecidableEq β]

lemma card_sub {i : β} {s : Finset β} (hi : i ∈ s) :
    #(s.subtype (· ≠ i)) = #s - 1 := by
  rw [card_subtype, filter_ne', card_erase_of_mem hi]

lemma card_inter_sub {i : β} {s t : Finset β} (hs : i ∈ s) (ht : i ∈ t) :
    #(s.subtype (· ≠ i) ∩ t.subtype (· ≠ i)) = #(s ∩ t) - 1 := by
  rw [← card_map (Function.Embedding.subtype _), map_inter, subtype_map, subtype_map,
    ← filter_inter_distrib, filter_ne', card_erase_of_mem (mem_inter.2 ⟨hs, ht⟩)]

lemma sub_inj {i : β} {s t : Finset β} (hs : i ∈ s) (ht : i ∈ t)
    (h : s.subtype (· ≠ i) = t.subtype (· ≠ i)) : s = t := by
  have h2 := congrArg (fun u => u.map (Function.Embedding.subtype (· ≠ i))) h
  simp only [subtype_map, filter_ne'] at h2
  rw [← insert_erase hs, ← insert_erase ht, h2]

lemma double_count [Fintype β] (C : Finset (Finset β)) :
    ∑ s ∈ C, #s = ∑ i, #(C.filter (fun s => i ∈ s)) := by
  calc ∑ s ∈ C, #s = ∑ s ∈ C, ∑ i, (if i ∈ s then 1 else 0) := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_boole]; simp
    _ = ∑ i, ∑ s ∈ C, (if i ∈ s then 1 else 0) := sum_comm
    _ = ∑ i, #(C.filter (fun s => i ∈ s)) := by
        refine sum_congr rfl fun i _ => ?_
        rw [sum_boole]; simp

/-- Johnson's bound for constant-weight codes of minimum distance 4, on any finite type. -/
theorem main : ∀ (n : ℕ) (β : Type) [Fintype β] [DecidableEq β], Fintype.card β = n →
    ∀ (k : ℕ) (C : Finset (Finset β)), (∀ s ∈ C, #s = k) →
    (∀ s ∈ C, ∀ t ∈ C, s ≠ t → #(s ∩ t) + 2 ≤ k) → #C ≤ johnsonBound n 4 k := by
  intro n
  induction n with
  | zero =>
    intro β _ _ hβ k C _ _
    have : IsEmpty β := Fintype.card_eq_zero_iff.mp hβ
    simp only [johnsonBound]
    apply card_le_one.mpr
    intro a _ b _
    ext x; exact isEmptyElim x
  | succ n ih =>
    intro β _ _ hβ k C hk hC
    cases k with
    | zero =>
      simp only [johnsonBound]
      apply card_le_one.mpr
      intro a ha b hb
      rw [card_eq_zero.mp (hk a ha), card_eq_zero.mp (hk b hb)]
    | succ w =>
      simp only [johnsonBound]
      split_ifs with hw
      · apply card_le_one.mpr
        intro a ha b hb
        by_contra hab
        have := hC a ha b hb hab
        omega
      · rw [Nat.le_div_iff_mul_le (Nat.succ_pos w)]
        have hsum : ∑ s ∈ C, #s = #C * (w + 1) := by
          rw [sum_congr rfl hk, sum_const, smul_eq_mul]
        have hi : ∀ i : β, #(C.filter (fun s => i ∈ s)) ≤ johnsonBound n 4 w := by
          intro i
          have hinj : Set.InjOn (fun s : Finset β => s.subtype (· ≠ i))
              (C.filter (fun s => i ∈ s) : Set (Finset β)) := by
            intro s hs t ht h
            exact sub_inj (mem_filter.1 hs).2 (mem_filter.1 ht).2 h
          rw [← card_image_of_injOn hinj]
          refine ih {x // x ≠ i} ?_ w _ ?_ ?_
          · rw [Fintype.card_subtype, filter_ne', card_erase_of_mem (mem_univ i), card_univ, hβ]
            omega
          · intro u hu
            obtain ⟨s, hs, rfl⟩ := mem_image.1 hu
            have hs' := mem_filter.1 hs
            rw [card_sub hs'.2, hk s hs'.1]
            omega
          · intro u hu v hv huv
            obtain ⟨s, hs, rfl⟩ := mem_image.1 hu
            obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
            have hs' := mem_filter.1 hs
            have ht' := mem_filter.1 ht
            have hst : s ≠ t := fun h => huv (by rw [h])
            have h1 := hC s hs'.1 t ht'.1 hst
            have h2 : 1 ≤ #(s ∩ t) := card_pos.2 ⟨i, mem_inter.2 ⟨hs'.2, ht'.2⟩⟩
            rw [card_inter_sub hs'.2 ht'.2]
            omega
        calc #C * (w + 1) = ∑ s ∈ C, #s := hsum.symm
          _ = ∑ i, #(C.filter (fun s => i ∈ s)) := double_count C
          _ ≤ ∑ _i : β, johnsonBound n 4 w := sum_le_sum fun i _ => hi i
          _ = (n + 1) * johnsonBound n 4 w := by rw [sum_const, card_univ, hβ, smul_eq_mul]

end JB

/-- Johnson's bound for the independence number of the Johnson graph. -/
lemma indepNum_johnson_le_johnsonBound : α(J(n, k)) ≤ johnsonBound n 4 k := by
  obtain ⟨S, hS⟩ := (J(n, k)).exists_isNIndepSet_indepNum
  rw [← hS.card_eq, ← card_map (Function.Embedding.subtype _)]
  refine JB.main n (Fin n) (Fintype.card_fin n) k _ ?_ ?_
  · intro s hs
    obtain ⟨x, -, rfl⟩ := mem_map.1 hs
    exact x.2
  · intro s hs t ht hst
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hs
    obtain ⟨y, hy, rfl⟩ := mem_map.1 ht
    have hxy : x ≠ y := fun h => hst (by rw [h])
    have hna : ¬ (J(n, k)).Adj x y := hS.isIndepSet (mem_coe.2 hx) (mem_coe.2 hy) hxy
    change ¬ (#(x.val ∩ y.val) + 1 = k) at hna
    have hle : #(x.val ∩ y.val) ≤ k :=
      calc _ ≤ #x.val := card_le_card inter_subset_left
        _ = k := x.2
    have hlt : #(x.val ∩ y.val) < k := by
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso; apply hxy
        have h1 : x.val ∩ y.val = x.val :=
          eq_of_subset_of_card_le inter_subset_left (by rw [h, x.2])
        have h2 : x.val ⊆ y.val := by rw [← h1]; exact inter_subset_right
        exact Subtype.ext (eq_of_subset_of_card_le h2 (by rw [x.2, y.2]))
    simp only [Function.Embedding.coe_subtype]
    omega

end Erdos835

#print axioms Erdos835.indepNum_johnson_le_johnsonBound
