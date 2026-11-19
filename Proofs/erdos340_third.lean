import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Function Set

section Restated
/-! Restated verbatim from FormalConjecturesForMathlib/Combinatorics/Basic.lean (data only;
the existence proof inside `greedySidon.go` is our own). -/

variable {α : Type*} [AddCommMonoid α]

def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Finset

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

end Finset

namespace Erdos340

/-- Covering map: every element that cannot be added to a Sidon set `A` lies in `g '' A³`. -/
def g (t : ℕ × ℕ × ℕ) : ℕ :=
  if t.2.1 < t.1 ∧ t.2.2 = t.1 then (t.1 + t.2.1) / 2 else t.1 + t.2.1 - t.2.2

lemma g_le (t : ℕ × ℕ × ℕ) : g t ≤ t.1 + t.2.1 := by
  unfold g; split_ifs <;> omega

lemma insert_sidon (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (x : ℕ)
    (hx : x ∉ (A ×ˢ A ×ˢ A).image g) : IsSidon ((insert x A : Finset ℕ) : Set ℕ) := by
  have hmem : ∀ b ∈ A, ∀ c ∈ A, ∀ a ∈ A, g (b, c, a) ≠ x := by
    intro b hb c hc a ha h
    exact hx (Finset.mem_image.2 ⟨(b, c, a), by simp [hb, hc, ha], h⟩)
  have hxA : x ∉ A := by
    intro h
    exact hmem x h x h x h (by simp [g])
  have F1 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, x + a ≠ b + c := by
    intro a ha b hb c hc h
    by_cases hcb : c < b ∧ a = b
    · exact hxA (by rw [show x = c by omega]; exact hc)
    · apply hmem b hb c hc a ha
      simp only [g, hcb, if_false]
      omega
  have F2 : ∀ b ∈ A, ∀ c ∈ A, x + x ≠ b + c := by
    intro b hb c hc h
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · apply hmem b hb c hc b hb
      simp only [g, hcb, and_self, if_true]
      omega
    · exact hxA (by rw [show x = b by omega]; exact hb)
    · apply hmem c hc b hb c hc
      simp only [g, hcb, and_self, if_true]
      omega
  intro i₁ hi1 j₁ hj1 i₂ hi2 j₂ hj2 heq
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi1 hj1 hi2 hj2
  rcases hi1 with hi1 | hi1 <;> rcases hj1 with hj1 | hj1 <;>
    rcases hi2 with hi2 | hi2 <;> rcases hj2 with hj2 | hj2
  all_goals first
    | omega
    | exact hA _ hi1 _ hj1 _ hi2 _ hj2 heq
    | (exfalso; first
        | exact F1 _ hi2 _ hj1 _ hj2 (by omega)
        | exact F1 _ hi1 _ hj1 _ hj2 (by omega)
        | exact F1 _ hj2 _ hi1 _ hi2 (by omega)
        | exact F1 _ hj1 _ hi1 _ hi2 (by omega)
        | exact F2 _ hj1 _ hj2 (by omega)
        | exact F2 _ hi1 _ hi2 (by omega))

lemma union_single (A : Finset ℕ) (m : ℕ) : A ∪ {m} = insert m A := by
  rw [Finset.union_comm, ← Finset.insert_eq]

lemma exists_big (A : Finset ℕ) (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
  refine ⟨2 * A.max' h + 1 + m, by omega, fun hm ↦ ?_, ?_⟩
  · have := A.le_max' _ hm
    omega
  · rw [union_single]
    apply insert_sidon A hA
    intro hx
    obtain ⟨t, ht, he⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_product] at ht
    have h1 := A.le_max' _ ht.1
    have h2 := A.le_max' _ ht.2.1
    have := g_le t
    omega

end Erdos340

namespace Finset

def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    have : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) :=
      Erdos340.exists_big A h hA m
    ⟨Nat.find this, Nat.find_spec this⟩
  else ⟨m, by simp_all [IsSidon]⟩

def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A.1 ∪ {s'.1}, s'.2.2.2⟩, s'.1)

def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

end Finset

end Restated

open Filter Finset

namespace Erdos340

lemma go_min (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (h : A.Nonempty) (m m' : ℕ)
    (h1 : m ≤ m') (h2 : m' < (greedySidon.go A hA m).1) (h3 : m' ∉ A) :
    ¬ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
  intro hs
  unfold greedySidon.go at h2
  rw [dif_pos h] at h2
  exact Nat.find_min _ h2 ⟨h1, h3, hs⟩

lemma aux_ne (k : ℕ) : (greedySidon.aux k).1.1.Nonempty := by
  cases k with
  | zero => exact ⟨1, by simp [greedySidon.aux]⟩
  | succ j =>
    rcases hp : greedySidon.aux j with ⟨⟨A, hA⟩, s⟩
    simp [greedySidon.aux, hp]

lemma aux_succ' (k : ℕ) : ∀ p, greedySidon.aux k = p → ∀ h : p.1.1.Nonempty,
    (greedySidon.aux (k+1)).2 = (greedySidon.go p.1.1 p.1.2 (p.1.1.max' h + 1)).1 ∧
    (greedySidon.aux (k+1)).1.1 = p.1.1 ∪ {(greedySidon.aux (k+1)).2} := by
  rintro ⟨⟨A, hA⟩, s⟩ hp h
  simp [greedySidon.aux, hp, h]
  generalize greedySidon.aux k = q at hp ⊢
  subst hp
  rw [dif_pos (show A.Nonempty from h)]

lemma aux_succ (k : ℕ) :
    (greedySidon.aux (k+1)).2 = (greedySidon.go (greedySidon.aux k).1.1 (greedySidon.aux k).1.2
      ((greedySidon.aux k).1.1.max' (aux_ne k) + 1)).1 ∧
    (greedySidon.aux (k+1)).1.1 = (greedySidon.aux k).1.1 ∪ {(greedySidon.aux (k+1)).2} :=
  aux_succ' k _ rfl (aux_ne k)

lemma step_ge (k : ℕ) :
    (greedySidon.aux k).1.1.max' (aux_ne k) + 1 ≤ (greedySidon.aux (k+1)).2 := by
  have hv := (greedySidon.go (greedySidon.aux k).1.1 (greedySidon.aux k).1.2
      ((greedySidon.aux k).1.1.max' (aux_ne k) + 1)).2.1
  rw [← (aux_succ k).1] at hv
  exact hv

lemma a_spec (k : ℕ) : (∀ x ∈ (greedySidon.aux k).1.1, x ≤ (greedySidon.aux k).2) ∧
    (greedySidon.aux k).2 ∈ (greedySidon.aux k).1.1 := by
  induction k with
  | zero => simp [greedySidon.aux]
  | succ k ih =>
    have hv := step_ge k
    rw [(aux_succ k).2]
    constructor
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · have := (greedySidon.aux k).1.1.le_max' x hx
        omega
      · rw [Finset.mem_singleton.1 hx]
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma a_lt (k : ℕ) : (greedySidon.aux k).2 < (greedySidon.aux (k+1)).2 := by
  have h1 := (greedySidon.aux k).1.1.le_max' _ (a_spec k).2
  have h2 := step_ge k
  omega

lemma a_ge (k : ℕ) : k + 1 ≤ (greedySidon.aux k).2 := by
  induction k with
  | zero => show 1 ≤ 1; exact le_refl _
  | succ k ih => have := a_lt k; omega

lemma minimal (k m : ℕ) (h1 : (greedySidon.aux k).2 < m) (h2 : m < (greedySidon.aux (k+1)).2) :
    ¬ IsSidon (↑((greedySidon.aux k).1.1 ∪ {m}) : Set ℕ) := by
  have hmax := (a_spec k).1 _ ((greedySidon.aux k).1.1.max'_mem (aux_ne k))
  refine go_min (greedySidon.aux k).1.1 (greedySidon.aux k).1.2 (aux_ne k)
    ((greedySidon.aux k).1.1.max' (aux_ne k) + 1) m (by omega) ?_ ?_
  · rw [← (aux_succ k).1]
    exact h2
  · intro hm
    have := (a_spec k).1 m hm
    omega

lemma mono (k : ℕ) : (greedySidon.aux k).1.1 ⊆ (greedySidon.aux (k+1)).1.1 := by
  rw [(aux_succ k).2]
  exact Finset.subset_union_left

lemma img_mono {A B : Finset ℕ} (h : A ⊆ B) :
    (A ×ˢ A ×ˢ A).image g ⊆ (B ×ˢ B ×ˢ B).image g :=
  Finset.image_subset_image (Finset.product_subset_product h (Finset.product_subset_product h h))

lemma self_mem {A : Finset ℕ} {m : ℕ} (h : m ∈ A) : m ∈ (A ×ˢ A ×ˢ A).image g :=
  Finset.mem_image.2 ⟨(m, m, m), by simp [h], by simp [g]⟩

lemma cover (k : ℕ) : ∀ m, 1 ≤ m → m < (greedySidon.aux (k+1)).2 →
    m ∈ ((greedySidon.aux k).1.1 ×ˢ (greedySidon.aux k).1.1 ×ˢ (greedySidon.aux k).1.1).image g := by
  induction k with
  | zero =>
    intro m h1 h2
    rcases lt_trichotomy m (greedySidon.aux 0).2 with h | h | h
    · exact absurd h (by show ¬ m < 1; omega)
    · apply self_mem; rw [h]; exact (a_spec 0).2
    · by_contra hn
      exact minimal 0 m h h2 (by rw [union_single]; exact insert_sidon _ (greedySidon.aux 0).1.2 m hn)
  | succ k ih =>
    intro m h1 h2
    rcases lt_trichotomy m (greedySidon.aux (k+1)).2 with h | h | h
    · exact img_mono (mono k) (ih m h1 h)
    · apply self_mem; rw [h]; exact (a_spec (k+1)).2
    · by_contra hn
      exact minimal (k+1) m h h2
        (by rw [union_single]; exact insert_sidon _ (greedySidon.aux (k+1)).1.2 m hn)

lemma mem_range (k : ℕ) : ∀ x ∈ (greedySidon.aux k).1.1, ∃ j, (greedySidon.aux j).2 = x := by
  induction k with
  | zero =>
    intro x hx
    have h0 : (greedySidon.aux 0).1.1 = {1} := rfl
    rw [h0] at hx
    exact ⟨0, (Finset.mem_singleton.1 hx).symm⟩
  | succ k ih =>
    intro x hx
    rw [(aux_succ k).2] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact ih x hx
    · exact ⟨k+1, (Finset.mem_singleton.1 hx).symm⟩

lemma count_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℕ, n ≤ c ^ 3 ∧ c ≤ (Set.range greedySidon ∩ Set.Icc 1 n).ncard := by
  classical
  have hex : ∃ k, n < (greedySidon.aux (k+1)).2 := ⟨n, by have := a_ge (n+1); omega⟩
  obtain ⟨k, hk1, hkmin⟩ : ∃ k, n < (greedySidon.aux (k+1)).2 ∧
      ∀ j < k, ¬ n < (greedySidon.aux (j+1)).2 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ Nat.find_min hex hj⟩
  have hk2 : (greedySidon.aux k).2 ≤ n := by
    rcases k with _ | j
    · show 1 ≤ n
      exact hn
    · exact not_lt.1 (hkmin j (Nat.lt_succ_self j))
  refine ⟨(greedySidon.aux k).1.1.card, ?_, ?_⟩
  · have hcov : Finset.Icc 1 n ⊆ ((greedySidon.aux k).1.1 ×ˢ (greedySidon.aux k).1.1 ×ˢ
        (greedySidon.aux k).1.1).image g := fun m hm ↦ by
      rw [Finset.mem_Icc] at hm
      exact cover k m hm.1 (by omega)
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_image_le (s := (greedySidon.aux k).1.1 ×ˢ (greedySidon.aux k).1.1 ×ˢ
        (greedySidon.aux k).1.1) (f := g)
    rw [Finset.card_product, Finset.card_product] at h2
    rw [Nat.card_Icc] at h1
    have h3 : (greedySidon.aux k).1.1.card * ((greedySidon.aux k).1.1.card *
        (greedySidon.aux k).1.1.card) = (greedySidon.aux k).1.1.card ^ 3 := by ring
    omega
  · rw [← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard
    · intro x hx
      rw [Finset.mem_coe] at hx
      obtain ⟨j, hj⟩ := mem_range k x hx
      refine ⟨⟨j, hj⟩, ?_, ?_⟩
      · have := a_ge j
        omega
      · have := (a_spec k).1 x hx
        omega
    · exact (Set.finite_Icc 1 n).subset Set.inter_subset_right

theorem erdos_340.variants.third (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 3)) =O[atTop]
      fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨c, hc, hle⟩ := count_bound n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  calc (n : ℝ) ^ ((1 : ℝ) / 3) ≤ ((c : ℝ) ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hc) (by norm_num)
    _ = c := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)
    _ ≤ _ := by exact_mod_cast hle

end Erdos340

#print axioms Erdos340.erdos_340.variants.third
