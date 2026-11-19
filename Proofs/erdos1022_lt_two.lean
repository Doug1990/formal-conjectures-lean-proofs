import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Finset

def HasPropertyB {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∃ f : α → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

variable {V : Type*} [DecidableEq V]

def hypergraphInduce (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter (· ⊆ S)

end Finset

namespace Erdos1022

def SparseImpliesPropertyB (t : ℕ) (c : ℝ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ A ∈ F, t ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → ((F.hypergraphInduce X).card : ℝ) < c * (X.card : ℝ)) →
    F.HasPropertyB

namespace LT2

def code (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

lemma code_inj : Function.Injective code := by
  intro a b h
  have := congrArg (fun n => n.bitIndices.toFinset) h
  simpa [code] using this

lemma lt_code {s : Finset ℕ} {b : ℕ} (hb : b ∈ s) : b < code s :=
  lt_of_lt_of_le (Nat.lt_two_pow_self (n := b))
    (Finset.single_le_sum (f := fun i => 2 ^ i) (fun _ _ => Nat.zero_le _) hb)

def ap (p : Finset ℕ × Finset ℕ) : ℕ := Nat.pair (code p.1) (code p.2) + 1

lemma ap_inj : Function.Injective ap := by
  intro p q h
  have h' : Nat.pair (code p.1) (code p.2) = Nat.pair (code q.1) (code q.2) := by
    unfold ap at h; omega
  have := congrArg Nat.unpair h'
  rw [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at this
  exact Prod.ext (code_inj this.1) (code_inj this.2)

lemma lt_ap1 {p : Finset ℕ × Finset ℕ} {b : ℕ} (hb : b ∈ p.1) : b < ap p := by
  have := lt_code hb
  have := Nat.left_le_pair (code p.1) (code p.2)
  unfold ap; omega

lemma lt_ap2 {p : Finset ℕ × Finset ℕ} {b : ℕ} (hb : b ∈ p.2) : b < ap p := by
  have := lt_code hb
  have := Nat.right_le_pair (code p.1) (code p.2)
  unfold ap; omega

variable (k : ℕ)

def W : Finset ℕ := Finset.range (2 * k + 1)
def S1 : Finset (Finset ℕ × Finset ℕ) := (W k).powersetCard k ×ˢ (W k).powersetCard k
def L1 : Finset ℕ := (S1 k).image ap
def S2 : Finset (Finset ℕ × Finset ℕ) := (W k).powersetCard k ×ˢ (L1 k).powersetCard k
def S : Finset (Finset ℕ × Finset ℕ) := S1 k ∪ S2 k
def F : Finset (Finset ℕ) :=
  (S k).biUnion (fun p => ({insert (ap p) p.1, insert (ap p) p.2} : Finset (Finset ℕ)))

variable {k}

lemma S_card {p : Finset ℕ × Finset ℕ} (hp : p ∈ S k) : p.1.card = k ∧ p.2.card = k := by
  rcases Finset.mem_union.1 hp with h | h
  · simp only [S1, Finset.mem_product, Finset.mem_powersetCard] at h
    exact ⟨h.1.2, h.2.2⟩
  · simp only [S2, Finset.mem_product, Finset.mem_powersetCard] at h
    exact ⟨h.1.2, h.2.2⟩

lemma F_card {A : Finset ℕ} (hA : A ∈ F k) : k ≤ A.card := by
  obtain ⟨p, hp, hAp⟩ := Finset.mem_biUnion.1 hA
  have hc := S_card hp
  rcases Finset.mem_insert.1 hAp with h | h
  · rw [h]
    calc k = p.1.card := hc.1.symm
      _ ≤ _ := Finset.card_le_card (Finset.subset_insert _ _)
  · rw [Finset.mem_singleton.1 h]
    calc k = p.2.card := hc.2.symm
      _ ≤ _ := Finset.card_le_card (Finset.subset_insert _ _)

lemma sparse (hk : 1 ≤ k) (X : Finset ℕ) (hX : X.Nonempty) :
    ((F k).filter (· ⊆ X)).card < 2 * X.card := by
  have hsub : (F k).filter (· ⊆ X) ⊆ ((S k).filter (fun p => ap p ∈ X.erase (X.min' hX))).biUnion
      (fun p => ({insert (ap p) p.1, insert (ap p) p.2} : Finset (Finset ℕ))) := by
    intro A hA
    rw [Finset.mem_filter] at hA
    obtain ⟨hAF, hAX⟩ := hA
    obtain ⟨p, hp, hAp⟩ := Finset.mem_biUnion.1 hAF
    refine Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩, hAp⟩
    have hc := S_card hp
    obtain ⟨b, hbA, hb, hvA⟩ : ∃ b ∈ A, b < ap p ∧ ap p ∈ A := by
      rcases Finset.mem_insert.1 hAp with h | h
      · rw [h]
        obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < p.1.card)
        exact ⟨b, Finset.mem_insert_of_mem hb, lt_ap1 hb, Finset.mem_insert_self _ _⟩
      · rw [Finset.mem_singleton.1 h]
        obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < p.2.card)
        exact ⟨b, Finset.mem_insert_of_mem hb, lt_ap2 hb, Finset.mem_insert_self _ _⟩
    refine Finset.mem_erase.2 ⟨?_, hAX hvA⟩
    intro he
    have := X.min'_le b (hAX hbA)
    omega
  calc ((F k).filter (· ⊆ X)).card
      ≤ (((S k).filter (fun p => ap p ∈ X.erase (X.min' hX))).biUnion
          (fun p => ({insert (ap p) p.1, insert (ap p) p.2} : Finset (Finset ℕ)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ (S k).filter (fun p => ap p ∈ X.erase (X.min' hX)),
          ({insert (ap p) p.1, insert (ap p) p.2} : Finset (Finset ℕ)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (S k).filter (fun p => ap p ∈ X.erase (X.min' hX)), 2 :=
        Finset.sum_le_sum (fun p _ => (Finset.card_insert_le _ _).trans
          (by rw [Finset.card_singleton]))
    _ = 2 * ((S k).filter (fun p => ap p ∈ X.erase (X.min' hX))).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * (X.erase (X.min' hX)).card :=
        Nat.mul_le_mul_left 2 (Finset.card_le_card_of_injOn ap
          (fun p hp => (Finset.mem_filter.1 hp).2) (fun a _ b _ h => ap_inj h))
    _ < 2 * X.card := by
        rw [Finset.card_erase_of_mem (X.min'_mem hX)]
        have := hX.card_pos
        omega

lemma mono {f : ℕ → Fin 2} {c : Fin 2} {v : ℕ} {P : Finset ℕ} (hv : f v = c)
    (hP : ∀ x ∈ P, f x = c) : ∀ x ∈ insert v P, ∀ y ∈ insert v P, f x = f y := by
  intro x hx y hy
  rw [Finset.mem_insert] at hx hy
  have h1 : f x = c := by
    rcases hx with rfl | hx
    · exact hv
    · exact hP x hx
  have h2 : f y = c := by
    rcases hy with rfl | hy
    · exact hv
    · exact hP y hy
  rw [h1, h2]

lemma fin2 {a b c : Fin 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  apply Fin.ext
  have h1 : a.val ≠ c.val := fun h => ha (Fin.ext h)
  have h2 : b.val ≠ c.val := fun h => hb (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := c.isLt
  omega

lemma not_B (_hk : 1 ≤ k) : ¬ (F k).HasPropertyB := by
  rintro ⟨f, hf⟩
  have key : ∀ p ∈ S k, ∀ c, (∀ x ∈ p.1, f x = c) → f (ap p) ≠ c := by
    intro p hp c hc hv
    obtain ⟨x, hx, y, hy, hxy⟩ := hf (insert (ap p) p.1)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_insert_self _ _⟩)
    exact hxy (mono hv hc x hx y hy)
  have key2 : ∀ p ∈ S k, ∀ c, (∀ x ∈ p.2, f x = c) → f (ap p) ≠ c := by
    intro p hp c hc hv
    obtain ⟨x, hx, y, hy, hxy⟩ := hf (insert (ap p) p.2)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)
    exact hxy (mono hv hc x hx y hy)
  obtain ⟨c, R, hRW, hRc, hRcard⟩ :
      ∃ c : Fin 2, ∃ R ⊆ W k, (∀ x ∈ R, f x = c) ∧ k + 1 ≤ R.card := by
    have := Finset.card_filter_add_card_filter_not (s := W k) (p := fun x => f x = 0)
    have hW : (W k).card = 2 * k + 1 := Finset.card_range _
    by_cases h : k + 1 ≤ ((W k).filter (fun x => f x = 0)).card
    · exact ⟨0, _, Finset.filter_subset _ _, fun x hx => (Finset.mem_filter.1 hx).2, h⟩
    · refine ⟨1, (W k).filter (fun x => ¬ f x = 0), Finset.filter_subset _ _,
        fun x hx => ?_, by omega⟩
      exact fin2 (Finset.mem_filter.1 hx).2 (by decide)
  obtain ⟨P0, hP0R, hP0c⟩ := Finset.exists_subset_card_eq (show k ≤ R.card by omega)
  have hP0W : P0 ∈ (W k).powersetCard k := Finset.mem_powersetCard.2 ⟨hP0R.trans hRW, hP0c⟩
  have hP0mono : ∀ x ∈ P0, f x = c := fun x hx => hRc x (hP0R hx)
  set Q' := (R.powersetCard k).image (fun P => ap (P0, P)) with hQ'
  have hQ'card : k ≤ Q'.card := by
    rw [hQ', Finset.card_image_of_injective _ (fun a b h => by
      have := ap_inj h
      exact (Prod.mk.inj this).2), Finset.card_powersetCard]
    calc k ≤ k + 1 := Nat.le_succ k
      _ = (k + 1).choose k := (Nat.choose_succ_self_right k).symm
      _ ≤ R.card.choose k := Nat.choose_le_choose k hRcard
  have hQ'prop : ∀ x ∈ Q', x ∈ L1 k ∧ f x ≠ c := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
    have hP' := Finset.mem_powersetCard.1 hP
    have hPW : P ∈ (W k).powersetCard k := Finset.mem_powersetCard.2 ⟨hP'.1.trans hRW, hP'.2⟩
    have hmem : (P0, P) ∈ S1 k := Finset.mem_product.2 ⟨hP0W, hPW⟩
    exact ⟨Finset.mem_image.2 ⟨_, hmem, rfl⟩,
      key (P0, P) (Finset.mem_union.2 (Or.inl hmem)) c hP0mono⟩
  obtain ⟨Q, hQQ', hQc⟩ := Finset.exists_subset_card_eq hQ'card
  have hQL : Q ∈ (L1 k).powersetCard k :=
    Finset.mem_powersetCard.2 ⟨fun x hx => (hQ'prop x (hQQ' hx)).1, hQc⟩
  have hpS : (P0, Q) ∈ S k := Finset.mem_union.2 (Or.inr (Finset.mem_product.2 ⟨hP0W, hQL⟩))
  have h1 : f (ap (P0, Q)) ≠ c := key _ hpS c hP0mono
  exact key2 _ hpS (f (ap (P0, Q)))
    (fun x hx => fin2 (hQ'prop x (hQQ' hx)).2 h1) rfl

end LT2

theorem erdos_1022.variants.lt_two :
    ∀ (t : ℕ) (c : ℝ), SparseImpliesPropertyB t c → c < 2 := by
  intro t c h
  by_contra hc
  have hc' : (2 : ℝ) ≤ c := not_lt.1 hc
  apply LT2.not_B (k := t + 1) (by omega)
  apply h
  · intro A hA
    have := LT2.F_card hA
    omega
  · intro X hX
    have h1 := LT2.sparse (k := t + 1) (by omega) X hX
    have h2 : (((LT2.F (t + 1)).filter (· ⊆ X)).card : ℝ) < 2 * (X.card : ℝ) := by
      exact_mod_cast h1
    have h3 : (2 : ℝ) * X.card ≤ c * X.card := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)
    exact lt_of_lt_of_le h2 h3

theorem erdos_1022 :
    ¬ ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
      ∀ t : ℕ, SparseImpliesPropertyB t (c t) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨t, ht⟩ := (hc.eventually_ge_atTop 2).exists
  exact absurd (erdos_1022.variants.lt_two t _ (h t)) (not_lt.2 ht)

end Erdos1022

#print axioms Erdos1022.erdos_1022.variants.lt_two
#print axioms Erdos1022.erdos_1022
