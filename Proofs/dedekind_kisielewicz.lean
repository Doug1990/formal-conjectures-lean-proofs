import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Antichain
import Mathlib.Tactic.Common
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Finite.Lemmas

namespace DedekindNumber

open Finset

instance piFinBoolDecidableLE {n : ℕ} :
    DecidableRel (fun (a b : Fin n → Bool) => a ≤ b) :=
  fun a b => show Decidable (a ≤ b) from by
    rw [Pi.le_def]
    exact Fintype.decidableForallFintype

def M (n : ℕ) : ℕ :=
  Fintype.card {f : (Fin n → Bool) → Bool // Monotone f}

def IsSperner {n : ℕ} (A : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (fun s t => s ⊆ t) (A : Set (Finset (Fin n)))

instance isSpernerDecidable {n : ℕ} :
    DecidablePred (fun A : Finset (Finset (Fin n)) => IsSperner A) :=
  fun A => by
    unfold IsSperner IsAntichain Set.Pairwise
    simp only [Finset.mem_coe, Pi.compl_apply, compl_iff_not]
    exact inferInstance

def M' (n : ℕ) : ℕ :=
  Fintype.card {A : Finset (Finset (Fin n)) // IsSperner A}

def χ {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

def supp {n : ℕ} (v : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun i => v i = true)

def toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Finset (Fin n)) :=
  univ.filter (fun s =>
    f (χ s) = true ∧ ∀ t : Finset (Fin n), t ⊆ s → f (χ t) = true → s ⊆ t)

def fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (v : Fin n → Bool) : Bool :=
  decide (∃ s ∈ A, ∀ i ∈ s, v i = true)

lemma mem_supp_iff {n : ℕ} (v : Fin n → Bool) (i : Fin n) : i ∈ supp v ↔ v i = true := by
  simp [supp]

lemma toSperner_isSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (_ : Monotone f) :
    IsSperner (toSperner f) := by
  intro s hs t ht hst; simp_all +decide [ Finset.ext_iff]
  contrapose! hst; unfold toSperner at *; aesop

lemma fromSperner_monotone {n : ℕ} (A : Finset (Finset (Fin n))) (_ : IsSperner A) :
    Monotone (fromSperner A) := by
      intro v w hvw hfv
      obtain ⟨s, hsA, hs⟩ : ∃ s ∈ A, s ⊆ supp v := by
        unfold fromSperner at hfv
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
      have hs_w : s ⊆ supp w := by
        intro i hi; have := hs hi
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
        exact Bool.eq_false_imp_eq_true.mp fun a ↦ hvw i (hs hi)
      exact decide_eq_true
        ( ⟨ s, hsA, fun i hi => by simpa using Finset.mem_filter.mp ( hs_w hi ) |>.2 ⟩ )

lemma exists_minimal_true_subset {n : ℕ} {f : (Fin n → Bool) → Bool} (_ : Monotone f)
    {s : Finset (Fin n)} (hs : f (χ s) = true) :
    ∃ t, t ⊆ s ∧ f (χ t) = true ∧ ∀ u, u ⊆ t → f (χ u) = true → t ⊆ u := by
      obtain ⟨t, ht₁, ht₂⟩ :
        ∃ t ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true},
        ∀ u ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true}, t.card ≤ u.card := by
        apply_rules [ Set.exists_min_image ]
        · exact Set.toFinite _
        · exact ⟨ s, Finset.Subset.refl _, hs ⟩
      refine' ⟨ t, ht₁.1, ht₁.2, fun u hu hu' => _ ⟩
      exact Classical.not_not.1 fun h =>
        not_lt_of_ge ( ht₂ u ⟨ hu.trans ht₁.1, hu' ⟩ )
        ( Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.2 ⟨ hu, by aesop ⟩ )

lemma fromSperner_toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    fromSperner (toSperner f) = f := by
  funext v
  by_cases h : f v <;> simp_all +decide [ fromSperner ]
  · obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Finset (Fin n),
    t ⊆ Finset.univ.filter (fun i => v i = true) ∧
    f (χ t) = true ∧
    ∀ u : Finset (Fin n), u ⊆ t → f (χ u) = true → t ⊆ u := by
      apply exists_minimal_true_subset hf;
      convert h using 2
      exact funext fun i => by unfold χ; aesop;
    exact ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht₂.1, ht₂.2 ⟩,
    fun i hi => Finset.mem_filter.mp ( ht₁ hi ) |>.2 ⟩
  · intro s hs; contrapose! h; simp_all +decide [ toSperner ]
    refine' hf _ hs.1
    intro i; by_cases hi : i ∈ s <;> simp_all +decide [ χ ]

lemma toSperner_fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (hA : IsSperner A) :
    toSperner (fromSperner A) = A := by
  ext s; simp [toSperner, fromSperner]
  constructor <;> intro hs
  all_goals generalize_proofs at *
  · obtain ⟨ ⟨ t, ht₁, ht₂ ⟩, ht₃ ⟩ := hs
    convert ht₁ using 1
    exact subset_antisymm ( ht₃ t ( by unfold χ at ht₂; aesop ) t ht₁ ( by unfold χ; aesop ) )
      ( by unfold χ at ht₂; aesop )
  · refine' ⟨ ⟨ s, hs, _ ⟩, _ ⟩ <;> simp_all +decide [ IsSperner ]
    · exact fun i hi => by unfold χ; aesop
    · intro t ht x hx hx'; have := hA hx hs; simp_all +decide [ Finset.subset_iff, χ ]

def equivMonotoneSperner (n : ℕ) :
    {f : (Fin n → Bool) → Bool // Monotone f} ≃
    {A : Finset (Finset (Fin n)) // IsSperner A} where
  toFun := fun ⟨f, hf⟩ => ⟨toSperner f, toSperner_isSperner f hf⟩
  invFun := fun ⟨A, hA⟩ => ⟨fromSperner A, fromSperner_monotone A hA⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.ext (fromSperner_toSperner f hf)
  right_inv := fun ⟨A, hA⟩ => Subtype.ext (toSperner_fromSperner A hA)

theorem M_eq_M' : M  = M' := by
  ext n
  exact Fintype.card_congr (equivMonotoneSperner n)

def kisielewiczFormula (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 ^ (2 ^ n)), ∏ j ∈ Finset.Icc 1 (2 ^ n), ∏ i ∈ Finset.range j,
    (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat))

/-! ## Proof of the Kisielewicz formula -/

/-- bounded "bits of `i` are bits of `j`" -/
def Sub (i j : ℕ) : Prop := ∀ m ∈ range (i.log2 + 1), i.testBit m = true → j.testBit m = true

instance (i j : ℕ) : Decidable (Sub i j) := by unfold Sub; infer_instance

lemma factor_eq (i j m : ℕ) :
    (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat) =
      if (i.testBit m = true → j.testBit m = true) then 1 else 0 := by
  cases i.testBit m <;> cases j.testBit m <;> simp

lemma term_eq (k i j : ℕ) :
    1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat) =
      if ¬(k.testBit i = true ∧ k.testBit j = true ∧ Sub i j) then 1 else 0 := by
  have hp : ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat) =
      if Sub i j then 1 else 0 := by
    simp only [factor_eq, Finset.prod_boole]
    exact if_congr Iff.rfl rfl rfl
  rw [hp]
  cases k.testBit i <;> cases k.testBit j <;> by_cases h : Sub i j <;> simp [h]

def AC (n k : ℕ) : Prop :=
  ∀ j ∈ Icc 1 (2 ^ n), ∀ i ∈ range j, ¬(k.testBit i = true ∧ k.testBit j = true ∧ Sub i j)

instance (n k : ℕ) : Decidable (AC n k) := by unfold AC; infer_instance

lemma formula_eq (n : ℕ) : kisielewiczFormula n = #{k ∈ range (2 ^ 2 ^ n) | AC n k} := by
  rw [Finset.card_filter]
  unfold kisielewiczFormula
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [term_eq]
  simp only [Finset.prod_boole]
  exact if_congr Iff.rfl rfl rfl

lemma sub_iff' (i j : ℕ) : Sub i j ↔ ∀ m, i.testBit m = true → j.testBit m = true := by
  constructor
  · intro h m hm
    by_cases hlt : m < i.log2 + 1
    · exact h m (mem_range.2 hlt) hm
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le Nat.lt_log2_self
        (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hm
      exact absurd hm (by decide)
  · intro h m _
    exact h m

lemma testBit_sum (t : Finset ℕ) (m : ℕ) : (∑ i ∈ t, 2 ^ i).testBit m = true ↔ m ∈ t := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

variable {n : ℕ}

def enc (s : Finset (Fin n)) : ℕ := ∑ x ∈ s, 2 ^ (x : ℕ)

lemma enc_eq (s : Finset (Fin n)) : enc s = ∑ i ∈ s.map Fin.valEmbedding, 2 ^ i := by
  rw [enc, Finset.sum_map]; rfl

lemma testBit_enc (s : Finset (Fin n)) (m : ℕ) :
    (enc s).testBit m = true ↔ ∃ x ∈ s, (x : ℕ) = m := by
  rw [enc_eq, testBit_sum, Finset.mem_map]
  simp only [Fin.valEmbedding_apply]

lemma testBit_enc' (s : Finset (Fin n)) (x : Fin n) : (enc s).testBit x = true ↔ x ∈ s := by
  rw [testBit_enc]
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← Fin.ext h]
  · intro h
    exact ⟨x, h, rfl⟩

lemma enc_lt (s : Finset (Fin n)) : enc s < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases hb : (enc s).testBit i with _ | _
  · rfl
  · obtain ⟨x, -, hx⟩ := (testBit_enc s i).1 hb
    have := x.isLt
    omega

lemma enc_inj : Function.Injective (enc (n := n)) := by
  intro s t h
  ext x
  rw [← testBit_enc', ← testBit_enc', h]

def dec (i : ℕ) : Finset (Fin n) := Finset.univ.filter (fun x => i.testBit x = true)

lemma enc_dec {i : ℕ} (hi : i < 2 ^ n) : enc (dec (n := n) i) = i := by
  apply Nat.eq_of_testBit_eq
  intro m
  by_cases hm : m < n
  · have := testBit_enc' (dec (n := n) i) ⟨m, hm⟩
    simp only [dec, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact Bool.eq_iff_iff.2 this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (enc_lt _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

lemma sub_enc (s t : Finset (Fin n)) : Sub (enc s) (enc t) ↔ s ⊆ t := by
  rw [sub_iff']
  constructor
  · intro h x hx
    rw [← testBit_enc'] at hx ⊢
    exact h _ hx
  · intro h m hm
    obtain ⟨x, hx, rfl⟩ := (testBit_enc s m).1 hm
    exact (testBit_enc' t x).2 (h hx)

lemma enc_lt_of_ssubset {s t : Finset (Fin n)} (h : s ⊂ t) : enc s < enc t := by
  have hle : enc s ≤ enc t := by
    unfold enc
    exact Finset.sum_le_sum_of_subset h.1
  exact lt_of_le_of_ne hle (fun e => h.ne (enc_inj e))

def Enc (A : Finset (Finset (Fin n))) : ℕ := ∑ s ∈ A, 2 ^ enc s

lemma Enc_eq (A : Finset (Finset (Fin n))) :
    Enc A = ∑ i ∈ A.map ⟨enc, enc_inj⟩, 2 ^ i := by
  rw [Enc, Finset.sum_map]; rfl

lemma testBit_Enc (A : Finset (Finset (Fin n))) (m : ℕ) :
    (Enc A).testBit m = true ↔ ∃ s ∈ A, enc s = m := by
  rw [Enc_eq, testBit_sum, Finset.mem_map]
  rfl

lemma testBit_Enc' (A : Finset (Finset (Fin n))) (s : Finset (Fin n)) :
    (Enc A).testBit (enc s) = true ↔ s ∈ A := by
  rw [testBit_Enc]
  constructor
  · rintro ⟨t, ht, h⟩
    rwa [← enc_inj h]
  · intro h
    exact ⟨s, h, rfl⟩

lemma Enc_lt (A : Finset (Finset (Fin n))) : Enc A < 2 ^ 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases hb : (Enc A).testBit i with _ | _
  · rfl
  · obtain ⟨s, -, hs⟩ := (testBit_Enc A i).1 hb
    have := enc_lt s
    omega

def Dec (k : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter (fun s => k.testBit (enc s) = true)

lemma Enc_Dec {k : ℕ} (hk : k < 2 ^ 2 ^ n) : Enc (Dec (n := n) k) = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 2 ^ n
  · have := testBit_Enc' (Dec (n := n) k) (dec i)
    simp only [Dec, Finset.mem_filter, Finset.mem_univ, true_and, enc_dec hi] at this
    exact Bool.eq_iff_iff.2 this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Enc_lt _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

lemma Dec_Enc (A : Finset (Finset (Fin n))) : Dec (Enc A) = A := by
  ext s
  simp only [Dec, Finset.mem_filter, Finset.mem_univ, true_and]
  exact testBit_Enc' A s

lemma AC_Enc (A : Finset (Finset (Fin n))) : AC n (Enc A) ↔ IsSperner A := by
  constructor
  · intro h s hs t ht hst hsub
    have hlt := enc_lt_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩)
    have ht' := enc_lt t
    apply h (enc t) (by rw [mem_Icc]; omega) (enc s) (mem_range.2 hlt)
    exact ⟨(testBit_Enc' A s).2 hs, (testBit_Enc' A t).2 ht, (sub_enc s t).2 hsub⟩
  · intro h j _ i hi ⟨hki, hkj, hsub⟩
    obtain ⟨s, hs, rfl⟩ := (testBit_Enc A i).1 hki
    obtain ⟨t, ht, rfl⟩ := (testBit_Enc A j).1 hkj
    have hne : s ≠ t := by
      rintro rfl
      simp at hi
    have := h hs ht hne
    exact this ((sub_enc s t).1 hsub)

lemma M'_eq (n : ℕ) : M' n = #{k ∈ range (2 ^ 2 ^ n) | AC n k} := by
  rw [M', Fintype.card_subtype]
  apply Finset.card_bij' (fun A _ => Enc A) (fun k _ => Dec k)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Enc_lt A, (AC_Enc A).2 hA⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← AC_Enc, Enc_Dec hk.1]
    exact hk.2
  · intro A _
    exact Dec_Enc A
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact Enc_Dec hk.1

theorem M_eq_kisielewiczFormula : M = kisielewiczFormula := by
  rw [M_eq_M']
  funext n
  rw [M'_eq, formula_eq]

end DedekindNumber

#print axioms DedekindNumber.M_eq_kisielewiczFormula
