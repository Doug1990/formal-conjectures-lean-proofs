import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Lucas

open Finset

/-- Restated from the checkout (FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean). -/
abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

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

namespace CP

/-- Lucas: p ∤ C(pq + p − 1, p − 1). -/
lemma not_dvd (p q : ℕ) (hp : p.Prime) : ¬ p ∣ (p * q + (p - 1)).choose (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * q + (p - 1))
    (k := p - 1) (p := p)
  have e1 : (p * q + (p - 1)) % p = p - 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have e2 : (p * q + (p - 1)) / p = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have e3 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have e4 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [e1, e2, e3, e4, Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  intro hd
  have h0 := (Nat.dvd_iff_mod_eq_zero).1 hd
  unfold Nat.ModEq at h
  rw [h0, Nat.mod_eq_of_lt hp.one_lt] at h
  exact absurd h (by decide)

lemma not_dvd' (k p q : ℕ) (hp : p.Prime) (hq : k + 1 = p * q) :
    ¬ p ∣ (k + p).choose (k + 1) := by
  have hp2 := hp.two_le
  have : (k + p).choose (k + 1) = (p * q + (p - 1)).choose (p - 1) := by
    rw [show k + p = (k + 1) + (p - 1) by omega, Nat.choose_symm_add, hq]
  rw [this]
  exact not_dvd p q hp

variable {β : Type*} [DecidableEq β] [Fintype β]

omit [Fintype β] in
/-- Two different k-subsets of a (k+1)-set meet in k − 1 elements. -/
lemma inter_card (k : ℕ) (A B B' : Finset β) (hA : #A = k + 1) (hB : B ⊆ A) (hB' : B' ⊆ A)
    (hBk : #B = k) (hBk' : #B' = k) (hne : B ≠ B') : #(B ∩ B') + 1 = k := by
  have hu := card_union_add_card_inter B B'
  have hule : #(B ∪ B') ≤ k + 1 := hA ▸ card_le_card (union_subset hB hB')
  have hle : #(B ∩ B') ≤ k := hBk ▸ card_le_card inter_subset_left
  have hne' : #(B ∩ B') ≠ k := by
    intro h
    apply hne
    have h1 : B ∩ B' = B := eq_of_subset_of_card_le inter_subset_left (by rw [h, hBk])
    have h2 : B ⊆ B' := by rw [← h1]; exact inter_subset_right
    exact eq_of_subset_of_card_le h2 (by rw [hBk, hBk'])
  omega

omit [Fintype β] in
/-- Double counting of (k-set in F, (k+1)-set in V) incidences. -/
lemma dc (k : ℕ) (V : Finset β) (F : Finset (Finset β)) (hF : ∀ B ∈ F, #B = k) :
    ∑ A ∈ powersetCard (k + 1) V, #((powersetCard k A).filter (· ∈ F)) =
      #(F.filter (· ⊆ V)) * (#V - k) := by
  calc ∑ A ∈ powersetCard (k + 1) V, #((powersetCard k A).filter (· ∈ F))
      = ∑ A ∈ powersetCard (k + 1) V, ∑ B ∈ F, (if B ⊆ A then 1 else 0) := by
        refine sum_congr rfl fun A _ => ?_
        rw [sum_boole]
        congr 1
        ext B
        simp only [mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, hF B h1⟩, h1⟩
    _ = ∑ B ∈ F, ∑ A ∈ powersetCard (k + 1) V, (if B ⊆ A then 1 else 0) := sum_comm
    _ = ∑ B ∈ F, (if B ⊆ V then #V - k else 0) := by
        refine sum_congr rfl fun B hB => ?_
        rw [sum_boole]
        simp only [Nat.cast_id]
        split_ifs with hBV
        · -- the (k+1)-subsets of V containing B are insert x B, x ∈ V \ B
          have himg : (powersetCard (k + 1) V).filter (fun A => B ⊆ A) =
              (V \ B).image (fun x => insert x B) := by
            ext A
            simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
            constructor
            · rintro ⟨⟨hAV, hAc⟩, hBA⟩
              have hc := card_sdiff_add_card_eq_card hBA
              rw [hAc, hF B hB] at hc
              obtain ⟨x, hx⟩ := card_eq_one.1 (show #(A \ B) = 1 by omega)
              have hxA : x ∈ A \ B := by rw [hx]; exact mem_singleton_self x
              refine ⟨x, ⟨hAV (mem_sdiff.1 hxA).1, (mem_sdiff.1 hxA).2⟩, ?_⟩
              rw [insert_eq, ← hx, sdiff_union_of_subset hBA]
            · rintro ⟨x, ⟨hxV, hxB⟩, rfl⟩
              refine ⟨⟨insert_subset hxV hBV, ?_⟩, subset_insert x B⟩
              rw [card_insert_of_notMem hxB, hF B hB]
          rw [himg, card_image_of_injOn]
          · have := card_sdiff_add_card_eq_card hBV
            rw [hF B hB] at this
            omega
          · intro x hx y hy hxy
            simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hx hy
            have hxy' : insert x B = insert y B := hxy
            have : x ∈ insert y B := by
              rw [← hxy']; exact mem_insert_self x B
            rcases mem_insert.1 this with h | h
            · exact h
            · exact absurd h hx.2
        · rw [card_eq_zero, filter_eq_empty_iff]
          intro A hA hBA
          exact hBV (hBA.trans (mem_powersetCard.1 hA).1)
    _ = #(F.filter (· ⊆ V)) * (#V - k) := by
        rw [← sum_filter, sum_const, smul_eq_mul]

end CP

/--
Ma and Tang have proved that the chromatic number of $J(2k,k)$ is $>k+1$ for all $k>2$ not of the
form $p-1$ for prime $p$.
-/
theorem johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : (k + 1).Composite) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨c⟩ : (J(2 * k, k)).Colorable (k + 1) :=
    chromaticNumber_le_iff_colorable.mp (by exact_mod_cast hcon)
  obtain ⟨p, hpdef⟩ : ∃ p, p = (k + 1).minFac := ⟨_, rfl⟩
  have hp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
  have hplt : p < k + 1 := hpdef ▸ (Nat.not_prime_iff_minFac_lt (by omega)).1 h.2
  obtain ⟨q, hq⟩ : p ∣ k + 1 := hpdef ▸ Nat.minFac_dvd (k + 1)
  have hp2 := hp.two_le
  obtain ⟨V, hV⟩ := (powersetCard_nonempty (s := (univ : Finset (Fin (2 * k))))
    (n := k + p)).2 (by rw [card_univ, Fintype.card_fin]; omega)
  rw [mem_powersetCard] at hV
  let F : Finset (Finset (Fin (2 * k))) :=
    (univ.filter (fun v : {s : Finset (Fin (2 * k)) // #s = k} => c v = 0)).map
      (Function.Embedding.subtype _)
  have hF : ∀ B ∈ F, #B = k := by
    intro B hB
    obtain ⟨x, -, rfl⟩ := mem_map.1 hB
    exact x.2
  have hmemF : ∀ B (hB : #B = k), B ∈ F ↔ c ⟨B, hB⟩ = 0 := by
    intro B hB
    simp only [F, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro h; exact ⟨⟨B, hB⟩, h, rfl⟩
  -- every (k+1)-set contains exactly one k-set of colour 0
  have hone : ∀ A : Finset (Fin (2 * k)), #A = k + 1 →
      #((powersetCard k A).filter (· ∈ F)) = 1 := by
    intro A hA
    let g : Finset (Fin (2 * k)) → Fin (k + 1) := fun B =>
      if hB : #B = k then c ⟨B, hB⟩ else 0
    have hinj : Set.InjOn g (powersetCard k A : Set (Finset (Fin (2 * k)))) := by
      intro B hB B' hB' hgg
      rw [mem_coe, mem_powersetCard] at hB hB'
      by_contra hne
      have hadj : (J(2 * k, k)).Adj ⟨B, hB.2⟩ ⟨B', hB'.2⟩ :=
        CP.inter_card k A B B' hA hB.1 hB'.1 hB.2 hB'.2 hne
      apply c.valid hadj
      simpa [g, hB.2, hB'.2] using hgg
    have himg : (powersetCard k A).image g = univ := by
      apply eq_of_subset_of_card_le (subset_univ _)
      rw [card_image_of_injOn hinj, card_powersetCard, hA, card_univ, Fintype.card_fin,
        Nat.choose_succ_self_right]
    have hfilt : (powersetCard k A).filter (· ∈ F) = (powersetCard k A).filter (g · = 0) := by
      apply filter_congr
      intro B hB
      have hBk := (mem_powersetCard.1 hB).2
      rw [hmemF B hBk]
      simp [g, hBk]
    rw [hfilt]
    apply le_antisymm
    · apply card_le_one.2
      intro B hB B' hB'
      rw [mem_filter] at hB hB'
      exact hinj (mem_coe.2 hB.1) (mem_coe.2 hB'.1) (hB.2.trans hB'.2.symm)
    · have h0 : (0 : Fin (k + 1)) ∈ (powersetCard k A).image g := by rw [himg]; exact mem_univ _
      obtain ⟨B, hB, hgB⟩ := mem_image.1 h0
      exact card_pos.2 ⟨B, mem_filter.2 ⟨hB, hgB⟩⟩
  have hdc := CP.dc k V F hF
  rw [sum_congr rfl (fun A hA => hone A (mem_powersetCard.1 hA).2), sum_const,
    card_powersetCard, hV.2, smul_eq_mul, mul_one] at hdc
  have hdvd : p ∣ (k + p).choose (k + 1) :=
    ⟨#(F.filter (· ⊆ V)), by rw [hdc, show k + p - k = p by omega, mul_comm]⟩
  exact CP.not_dvd' k p q hp hq hdvd

/--
The smallest case not on this page is $k=9$:
But that one can be solved as well:
The chromatic number of $J(18, 9)$ is at least $11$.
-/
theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 :=
  johnson_chromaticNumber_composite 9 (by decide) ⟨by decide, by decide⟩

/-- Restated from the checkout. -/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))

namespace PI

variable {k : ℕ}

lemma T_map (A : Finset (Fin (2 * k))) (hA : #A = k + 1) :
    (({s : {s : Finset (Fin (2 * k)) // #s = k} | s.val ⊂ A} :
      Finset {s : Finset (Fin (2 * k)) // #s = k})).map (Function.Embedding.subtype _) =
      powersetCard k A := by
  ext B
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
    mem_powersetCard]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hs.subset, s.2⟩
  · rintro ⟨hBA, hB⟩
    refine ⟨⟨B, hB⟩, Finset.ssubset_iff_subset_ne.2 ⟨hBA, ?_⟩, rfl⟩
    intro h
    have h' : B = A := h
    rw [h', hA] at hB
    omega

lemma T_card (A : Finset (Fin (2 * k))) (hA : #A = k + 1) :
    #(({s : {s : Finset (Fin (2 * k)) // #s = k} | s.val ⊂ A} :
      Finset {s : Finset (Fin (2 * k)) // #s = k})) = k + 1 := by
  rw [← card_map (Function.Embedding.subtype _), T_map A hA, card_powersetCard, hA,
    Nat.choose_succ_self_right]

lemma T_adj (A : Finset (Fin (2 * k))) (hA : #A = k + 1)
    (s t : {s : Finset (Fin (2 * k)) // #s = k}) (hs : s.val ⊂ A) (ht : t.val ⊂ A)
    (hst : s ≠ t) : (J(2 * k, k)).Adj s t :=
  CP.inter_card k A s.val t.val hA hs.subset ht.subset s.2 t.2 (fun h => hst (Subtype.ext h))

lemma inj {α : Type*} (c : {s : Finset (Fin (2 * k)) // #s = k} → α)
    (hc : ∀ s t, (J(2 * k, k)).Adj s t → c s ≠ c t) (A : Finset (Fin (2 * k)))
    (hA : #A = k + 1) :
    Set.InjOn c ((({s : {s : Finset (Fin (2 * k)) // #s = k} | s.val ⊂ A} :
      Finset {s : Finset (Fin (2 * k)) // #s = k})) : Set _) := by
  intro s hs t ht hst
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  by_contra hne
  exact hc s t (T_adj A hA s t hs ht hne) hst

end PI

theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Property k := by
  rw [chromaticNumber_eq_iff_colorable_not_colorable]
  constructor
  · rintro ⟨⟨c⟩, -⟩
    refine ⟨fun s => c s, fun A hA => ?_⟩
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injOn (PI.inj (fun s => c s) (fun s t h => c.valid h) A hA),
      PI.T_card A hA, card_univ, Fintype.card_fin]
  · rintro ⟨c, hc⟩
    constructor
    · refine ⟨Coloring.mk c ?_⟩
      intro s t hadj
      have hadj' : #(s.val ∩ t.val) + 1 = k := hadj
      have hu := card_union_add_card_inter s.val t.val
      rw [s.2, t.2] at hu
      have hA : #(s.val ∪ t.val) = k + 1 := by omega
      have hst : s ≠ t := (J(2 * k, k)).ne_of_adj hadj
      have hss : ∀ u : {s : Finset (Fin (2 * k)) // #s = k}, u.val ⊆ s.val ∪ t.val →
          u.val ⊂ s.val ∪ t.val := by
        intro u hu'
        refine Finset.ssubset_iff_subset_ne.2 ⟨hu', fun h => ?_⟩
        have := u.2
        rw [h, hA] at this
        omega
      have himg := hc _ hA
      have hcard : #(image c ({u : {s : Finset (Fin (2 * k)) // #s = k} |
          u.val ⊂ s.val ∪ t.val} : Finset _)) =
          #(({u : {s : Finset (Fin (2 * k)) // #s = k} | u.val ⊂ s.val ∪ t.val} :
            Finset _)) := by
        rw [himg, PI.T_card _ hA, card_univ, Fintype.card_fin]
      have hinj := card_image_iff.1 hcard
      intro hct
      apply hst
      refine hinj ?_ ?_ hct
      · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        exact hss s subset_union_left
      · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
        exact hss t subset_union_right
    · rintro ⟨c'⟩
      obtain ⟨A, hA⟩ := (powersetCard_nonempty (s := (univ : Finset (Fin (2 * k))))
        (n := k + 1)).2 (by rw [card_univ, Fintype.card_fin]; omega)
      rw [mem_powersetCard] at hA
      have hinj := PI.inj (fun s => c' s) (fun s t h => c'.valid h) A hA.2
      have hle := card_le_card_of_injOn (fun s => c' s) (t := univ)
        (fun s _ => mem_coe.2 (mem_univ _)) hinj
      rw [PI.T_card A hA.2, card_univ, Fintype.card_fin] at hle
      omega

end Erdos835

#print axioms Erdos835.johnson_chromaticNumber_composite
#print axioms Erdos835.johnsonGraph_18_9_chromaticNumber
#print axioms Erdos835.property_iff_chromaticNumber
