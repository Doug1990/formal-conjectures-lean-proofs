import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin

namespace Erdos83

namespace P

variable (n : ℕ)

def σ (i : Fin (4 * n)) : Fin (4 * n) :=
  if h : (i : ℕ) < 2 * n then ⟨i + 2 * n, by omega⟩ else ⟨i - 2 * n, by omega⟩

lemma val_σ (i : Fin (4 * n)) :
    (σ n i : ℕ) = if (i : ℕ) < 2 * n then (i : ℕ) + 2 * n else (i : ℕ) - 2 * n := by
  unfold σ
  split_ifs <;> rfl

lemma σσ : Function.Involutive (σ n) := by
  intro i
  ext
  simp only [val_σ]
  split_ifs <;> omega

lemma σP (i : Fin (4 * n)) : ((σ n i : ℕ) < 2 * n) ↔ ¬ ((i : ℕ) < 2 * n) := by
  rw [val_σ]
  split_ifs <;> omega

def c (A : Finset (Fin (4 * n))) : ℕ :=
  (A.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n)).card

lemma c_le (A : Finset (Fin (4 * n))) : c n A ≤ A.card := Finset.card_filter_le _ _

lemma c_compl (A : Finset (Fin (4 * n))) :
    (A.filter (fun i : Fin (4 * n) => ¬ (i : ℕ) < 2 * n)).card = A.card - c n A := by
  have h := Finset.card_filter_add_card_filter_not (s := A) (fun i : Fin (4 * n) => (i : ℕ) < 2 * n)
  unfold c
  omega

lemma c_image (A : Finset (Fin (4 * n))) : c n (A.image (σ n)) = A.card - c n A := by
  have e : A.filter (fun a => (σ n a : ℕ) < 2 * n) =
      A.filter (fun a : Fin (4 * n) => ¬ ((a : ℕ) < 2 * n)) :=
    Finset.filter_congr (fun a _ => σP n a)
  have h := c_compl n A
  unfold c at h ⊢
  rw [Finset.filter_image, Finset.card_image_of_injective _ (σσ n).injective, e]
  exact h

lemma c_univ : c n Finset.univ = 2 * n := by
  have h1 := c_image n Finset.univ
  rw [Finset.image_univ_of_surjective (σσ n).surjective, Finset.card_univ,
    Fintype.card_fin] at h1
  omega

lemma image_image_σ (A : Finset (Fin (4 * n))) : (A.image (σ n)).image (σ n) = A := by
  rw [Finset.image_image]
  have : σ n ∘ σ n = id := funext (σσ n)
  rw [this, Finset.image_id]

lemma card_image_σ (A : Finset (Fin (4 * n))) : (A.image (σ n)).card = A.card :=
  Finset.card_image_of_injective _ (σσ n).injective

lemma mem_U (A : Finset (Fin (4 * n))) :
    A ∈ Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n))) ↔ A.card = 2 * n := by
  simp [Finset.mem_powersetCard]

/-- the two halves of the families have the same size -/
lemma card_FG :
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => n < c n A)).card =
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => c n A < n)).card := by
  refine Finset.card_bij' (fun A _ => A.image (σ n)) (fun A _ => A.image (σ n))
    ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_filter, mem_U] at hA ⊢
    refine ⟨by rw [card_image_σ]; exact hA.1, ?_⟩
    rw [c_image]
    have := c_le n A
    omega
  · intro A hA
    rw [Finset.mem_filter, mem_U] at hA ⊢
    refine ⟨by rw [card_image_σ]; exact hA.1, ?_⟩
    rw [c_image]
    have := c_le n A
    omega
  · intro A _
    exact image_image_σ n A
  · intro A _
    exact image_image_σ n A

lemma card_L :
    (Finset.univ.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n)).card = 2 * n :=
  c_univ n

lemma card_R :
    (Finset.univ.filter (fun i : Fin (4 * n) => ¬ (i : ℕ) < 2 * n)).card = 2 * n := by
  rw [c_compl, c_univ, Finset.card_univ, Fintype.card_fin]
  omega

lemma card_E :
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => c n A = n)).card = (2 * n).choose n ^ 2 := by
  classical
  have key : ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => c n A = n)).card =
      ((Finset.powersetCard n (Finset.univ.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n))) ×ˢ
        (Finset.powersetCard n
          (Finset.univ.filter (fun i : Fin (4 * n) => ¬ (i : ℕ) < 2 * n)))).card := by
    refine Finset.card_bij'
      (fun A _ => (A.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n),
        A.filter (fun i : Fin (4 * n) => ¬ (i : ℕ) < 2 * n)))
      (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter, mem_U] at hA
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      refine ⟨⟨Finset.filter_subset_filter _ (Finset.subset_univ _), hA.2⟩,
        ⟨Finset.filter_subset_filter _ (Finset.subset_univ _), ?_⟩⟩
      rw [c_compl]
      omega
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
      obtain ⟨⟨h1, h1c⟩, ⟨h2, h2c⟩⟩ := hp
      have hP1 : ∀ x ∈ p.1, (x : ℕ) < 2 * n := fun x hx => (Finset.mem_filter.mp (h1 hx)).2
      have hP2 : ∀ x ∈ p.2, ¬ (x : ℕ) < 2 * n := fun x hx => (Finset.mem_filter.mp (h2 hx)).2
      have hdisj : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact hP2 x hx2 (hP1 x hx1)
      rw [Finset.mem_filter, mem_U, Finset.card_union_of_disjoint hdisj, h1c, h2c]
      refine ⟨by omega, ?_⟩
      unfold c
      rw [Finset.filter_union, Finset.filter_true_of_mem hP1, Finset.filter_false_of_mem hP2,
        Finset.union_empty, h1c]
    · intro A _
      exact Finset.filter_union_filter_not_eq _ _
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
      obtain ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ := hp
      have hP1 : ∀ x ∈ p.1, (x : ℕ) < 2 * n := fun x hx => (Finset.mem_filter.mp (h1 hx)).2
      have hP2 : ∀ x ∈ p.2, ¬ (x : ℕ) < 2 * n := fun x hx => (Finset.mem_filter.mp (h2 hx)).2
      have hP1' : ∀ x ∈ p.1, ¬ ¬ (x : ℕ) < 2 * n := fun x hx h => h (hP1 x hx)
      refine Prod.ext ?_ ?_
      · show (p.1 ∪ p.2).filter _ = p.1
        rw [Finset.filter_union, Finset.filter_true_of_mem hP1, Finset.filter_false_of_mem hP2,
          Finset.union_empty]
      · show (p.1 ∪ p.2).filter _ = p.2
        rw [Finset.filter_union, Finset.filter_true_of_mem hP2, Finset.filter_false_of_mem hP1',
          Finset.empty_union]
  rw [key, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, card_L,
    card_R, sq]

lemma card_split :
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => n < c n A)).card +
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => c n A < n)).card +
    ((Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => c n A = n)).card = (4 * n).choose (2 * n) := by
  set U := Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n))) with hU
  have hUc : U.card = (4 * n).choose (2 * n) := by
    rw [hU, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_filter_add_card_filter_not (s := U) (fun A => n < c n A)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := U.filter (fun A => ¬ n < c n A)) (fun A => c n A < n)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : U.filter (fun A => ¬ n < c n A ∧ c n A < n) = U.filter (fun A => c n A < n) :=
    Finset.filter_congr (fun A _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩)
  have e2 : U.filter (fun A => ¬ n < c n A ∧ ¬ c n A < n) = U.filter (fun A => c n A = n) :=
    Finset.filter_congr (fun A _ => ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩)
  rw [e1, e2] at h2
  omega

end P

theorem erdos_83.variants.extremal (n : ℕ) :
    ∃ F : Finset (Finset (Fin (4 * n))), (∀ A ∈ F, A.card = 2 * n) ∧
      (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ∧
      F.card = ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 := by
  refine ⟨(Finset.powersetCard (2 * n) (Finset.univ : Finset (Fin (4 * n)))).filter
      (fun A => n < P.c n A), ?_, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_filter, P.mem_U] at hA
    exact hA.1
  · intro A hA B hB
    rw [Finset.mem_filter, P.mem_U] at hA hB
    set XA := A.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n) with hXA
    set XB := B.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n) with hXB
    have hcA : n < XA.card := hA.2
    have hcB : n < XB.card := hB.2
    have hsub : XA ∪ XB ⊆ Finset.univ.filter (fun i : Fin (4 * n) => (i : ℕ) < 2 * n) := by
      intro x hx
      rw [Finset.mem_union, hXA, hXB, Finset.mem_filter, Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      rcases hx with h | h
      · exact ⟨Finset.mem_univ _, h.2⟩
      · exact ⟨Finset.mem_univ _, h.2⟩
    have hU := Finset.card_le_card hsub
    rw [P.card_L] at hU
    have hui := Finset.card_union_add_card_inter XA XB
    have hint : XA ∩ XB ⊆ A ∩ B := by
      intro x hx
      rw [Finset.mem_inter, hXA, hXB, Finset.mem_filter, Finset.mem_filter] at hx
      exact Finset.mem_inter.mpr ⟨hx.1.1, hx.2.1⟩
    have := Finset.card_le_card hint
    omega
  · have h1 := P.card_split n
    have h2 := P.card_FG n
    have h3 := P.card_E n
    omega

end Erdos83

#print axioms Erdos83.erdos_83.variants.extremal
