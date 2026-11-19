import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat

namespace Erdos150

def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

namespace Sy

/-- Vertex 0 = u, vertex 1 = v, vertex 2+3j+t = position t on path j. -/
def R (a b : ℕ) : Prop :=
  (a = 0 ∧ 2 ≤ b ∧ (b - 2) % 3 = 0) ∨ (2 ≤ a ∧ b = a + 1 ∧ (a - 2) % 3 < 2) ∨
    (2 ≤ a ∧ (a - 2) % 3 = 2 ∧ b = 1)

variable (m : ℕ)

def G : SimpleGraph (Fin (3 * m + 2)) := SimpleGraph.fromRel fun x y => R x.1 y.1

variable {m}

def F (f : Fin m → Fin 3) (j : ℕ) : ℕ := if h : j < m then (f ⟨j, h⟩).1 else 0

lemma F_lt (f : Fin m → Fin 3) (j : ℕ) : F f j < 3 := by
  unfold F
  split
  · exact (f _).isLt
  · omega

lemma F_eq (f : Fin m → Fin 3) (j : Fin m) : F f j.1 = (f j).1 := by
  unfold F; rw [dif_pos j.2]

def T (f : Fin m → Fin 3) : Set (Fin (3 * m + 2)) :=
  {x | 2 ≤ x.1 ∧ (x.1 - 2) % 3 = F f ((x.1 - 2) / 3)}

def sd (F : ℕ → ℕ) (x : ℕ) : Prop := x = 1 ∨ (2 ≤ x ∧ F ((x - 2) / 3) < (x - 2) % 3)

lemma inv (F : ℕ → ℕ) (hF : ∀ j, F j < 3) (a b : ℕ) (h : R a b)
    (ha : ¬ (2 ≤ a ∧ (a - 2) % 3 = F ((a - 2) / 3)))
    (hb : ¬ (2 ≤ b ∧ (b - 2) % 3 = F ((b - 2) / 3))) : (sd F a ↔ sd F b) := by
  unfold sd
  rcases h with ⟨rfl, hb2, ht⟩ | ⟨ha2, rfl, ht⟩ | ⟨ha2, ht, rfl⟩
  · have := hF ((b - 2) / 3)
    omega
  · have e : (a + 1 - 2) / 3 = (a - 2) / 3 := by omega
    rw [e] at hb ⊢
    have := hF ((a - 2) / 3)
    omega
  · have := hF ((a - 2) / 3)
    omega

lemma not_pre (f : Fin m → Fin 3) : ¬ ((G m).induce (T f)ᶜ).Preconnected := by
  intro hpc
  have h0 : (⟨0, by omega⟩ : Fin (3 * m + 2)) ∈ (T f)ᶜ := fun h => Nat.not_succ_le_zero 1 h.1
  have h1 : (⟨1, by omega⟩ : Fin (3 * m + 2)) ∈ (T f)ᶜ := fun h => Nat.not_succ_le_self 1 h.1
  have key : ∀ (u w : ((T f)ᶜ : Set (Fin (3 * m + 2)))) (p : ((G m).induce (T f)ᶜ).Walk u w),
      (sd (F f) u.1.1 ↔ sd (F f) w.1.1) := by
    intro u w p
    induction p with
    | nil => exact Iff.rfl
    | @cons a b c hadj _ ih =>
      refine Iff.trans ?_ ih
      have h' : (G m).Adj a.1 b.1 := hadj
      rw [G, SimpleGraph.fromRel_adj] at h'
      rcases h'.2 with h | h
      · exact inv (F f) (F_lt f) _ _ h a.2 b.2
      · exact (inv (F f) (F_lt f) _ _ h b.2 a.2).symm
  obtain ⟨p⟩ := hpc ⟨_, h0⟩ ⟨_, h1⟩
  have := (key _ _ p).2 (Or.inl rfl)
  unfold sd at this
  simp only at this
  omega

lemma rstep {S : Set (Fin (3 * m + 2))} (x y : ℕ) (hx : x < 3 * m + 2) (hy : y < 3 * m + 2)
    (hxS : (⟨x, hx⟩ : Fin (3 * m + 2)) ∈ Sᶜ) (hyS : (⟨y, hy⟩ : Fin (3 * m + 2)) ∈ Sᶜ)
    (h : R x y) : ((G m).induce Sᶜ).Reachable ⟨_, hxS⟩ ⟨_, hyS⟩ := by
  apply SimpleGraph.Adj.reachable
  show (G m).Adj ⟨x, hx⟩ ⟨y, hy⟩
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl h⟩
  intro e
  simp only [Fin.mk.injEq] at e
  subst e
  unfold R at h
  omega

lemma down {S : Set (Fin (3 * m + 2))} (j : ℕ) (hj : j < m) (t : ℕ) (ht : t < 3)
    (h0 : (⟨0, by omega⟩ : Fin (3 * m + 2)) ∈ Sᶜ)
    (h : ∀ t', t' ≤ t → ∀ hb : 2 + 3 * j + t' < 3 * m + 2,
      (⟨2 + 3 * j + t', hb⟩ : Fin (3 * m + 2)) ∈ Sᶜ)
    (hb : 2 + 3 * j + t < 3 * m + 2) :
    ((G m).induce Sᶜ).Reachable ⟨_, h0⟩ ⟨_, h t le_rfl hb⟩ := by
  have s0 := rstep (S := S) 0 (2 + 3 * j + 0) (by omega) (by omega) h0
    (h 0 (by omega) (by omega)) (Or.inl ⟨rfl, by omega, by omega⟩)
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact s0
  · exact s0.trans (rstep _ _ _ _ _ _ (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · exact (s0.trans (rstep (2 + 3 * j + 0) (2 + 3 * j + 1) (by omega) (by omega) _
      (h 1 (by omega) (by omega)) (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))).trans
      (rstep _ _ _ _ _ _ (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))

lemma up {S : Set (Fin (3 * m + 2))} (j : ℕ) (hj : j < m) (t : ℕ) (ht : t < 3)
    (h1 : (⟨1, by omega⟩ : Fin (3 * m + 2)) ∈ Sᶜ)
    (h : ∀ t', t ≤ t' → t' < 3 → ∀ hb : 2 + 3 * j + t' < 3 * m + 2,
      (⟨2 + 3 * j + t', hb⟩ : Fin (3 * m + 2)) ∈ Sᶜ)
    (hb : 2 + 3 * j + t < 3 * m + 2) :
    ((G m).induce Sᶜ).Reachable ⟨_, h t le_rfl ht hb⟩ ⟨_, h1⟩ := by
  have s2 := rstep (S := S) (2 + 3 * j + 2) 1 (by omega) (by omega)
    (h 2 (by omega) (by omega) (by omega)) h1 (Or.inr (Or.inr ⟨by omega, by omega, rfl⟩))
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact ((rstep (2 + 3 * j + 0) (2 + 3 * j + 1) (by omega) (by omega) _
      (h 1 (by omega) (by omega) (by omega)) (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))).trans
      (rstep _ _ _ _ _ _ (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))).trans s2
  · exact (rstep _ _ _ _ _ _ (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))).trans s2
  · exact s2

lemma offT (f : Fin m → Fin 3) (j t' : ℕ) (hb : 2 + 3 * j + t' < 3 * m + 2) (ht : t' < 3)
    (hne : t' ≠ F f j) : (⟨2 + 3 * j + t', hb⟩ : Fin (3 * m + 2)) ∉ T f := by
  intro h
  change 2 ≤ 2 + 3 * j + t' ∧ (2 + 3 * j + t' - 2) % 3 = F f ((2 + 3 * j + t' - 2) / 3) at h
  have q : (2 + 3 * j + t' - 2) / 3 = j := by omega
  rw [q] at h
  omega

lemma pre (f : Fin m → Fin 3) (S : Set (Fin (3 * m + 2))) (hS : S ⊂ T f) :
    ((G m).induce Sᶜ).Preconnected := by
  obtain ⟨z, hzT, hzS⟩ := Set.exists_of_ssubset hS
  have sub := hS.1
  have notS : ∀ w, (w ∉ T f ∨ w = z) → w ∈ Sᶜ := fun w hw hwS =>
    hw.elim (fun h => h (sub hwS)) (fun e => hzS (e ▸ hwS))
  have h0 : (⟨0, by omega⟩ : Fin (3 * m + 2)) ∈ Sᶜ :=
    notS _ (Or.inl fun h => Nat.not_succ_le_zero 1 h.1)
  have h1 : (⟨1, by omega⟩ : Fin (3 * m + 2)) ∈ Sᶜ :=
    notS _ (Or.inl fun h => Nat.not_succ_le_self 1 h.1)
  have hz : 2 ≤ z.1 ∧ (z.1 - 2) % 3 = F f ((z.1 - 2) / 3) := hzT
  have hz2 := z.2
  have hj0 : (z.1 - 2) / 3 < m := by omega
  have pathfree : ∀ t', t' < 3 → ∀ hb : 2 + 3 * ((z.1 - 2) / 3) + t' < 3 * m + 2,
      (⟨2 + 3 * ((z.1 - 2) / 3) + t', hb⟩ : Fin (3 * m + 2)) ∈ Sᶜ := by
    intro t' ht' hb
    apply notS
    by_cases e : t' = F f ((z.1 - 2) / 3)
    · right
      ext
      show 2 + 3 * ((z.1 - 2) / 3) + t' = z.1
      omega
    · left
      exact offT f _ t' hb ht' e
  have reach1 : ((G m).induce Sᶜ).Reachable ⟨_, h0⟩ ⟨_, h1⟩ :=
    (down ((z.1 - 2) / 3) hj0 2 (by omega) h0 (fun t' ht' hb => pathfree t' (by omega) hb)
      (by omega)).trans
      (up ((z.1 - 2) / 3) hj0 2 (by omega) h1 (fun t' _ ht' hb => pathfree t' ht' hb) (by omega))
  suffices hall : ∀ a : (Sᶜ : Set (Fin (3 * m + 2))), ((G m).induce Sᶜ).Reachable ⟨_, h0⟩ a by
    intro a b
    exact (hall a).symm.trans (hall b)
  rintro ⟨⟨x, hx⟩, haS⟩
  by_cases e0 : x = 0
  · subst e0
    exact SimpleGraph.Reachable.refl _
  by_cases e1 : x = 1
  · subst e1
    exact reach1
  obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 3 ∧ x = 2 + 3 * j + t :=
    ⟨(x - 2) / 3, (x - 2) % 3, by omega, by omega⟩
  have hj : j < m := by omega
  by_cases hle : t ≤ F f j
  · have hyp : ∀ t', t' ≤ t → ∀ hb : 2 + 3 * j + t' < 3 * m + 2,
        (⟨2 + 3 * j + t', hb⟩ : Fin (3 * m + 2)) ∈ Sᶜ := by
      intro t' ht' hb
      rcases Nat.lt_or_eq_of_le ht' with hlt | rfl
      · exact notS _ (Or.inl (offT f j t' hb (by omega) (by omega)))
      · exact haS
    exact down j hj t ht h0 hyp hx
  · have hyp : ∀ t', t ≤ t' → t' < 3 → ∀ hb : 2 + 3 * j + t' < 3 * m + 2,
        (⟨2 + 3 * j + t', hb⟩ : Fin (3 * m + 2)) ∈ Sᶜ := by
      intro t' ht' ht3 hb
      rcases Nat.lt_or_eq_of_le ht' with hlt | rfl
      · exact notS _ (Or.inl (offT f j t' hb ht3 (by omega)))
      · exact haS
    exact reach1.trans (up j hj t ht h1 hyp hx).symm

lemma isMin (f : Fin m → Fin 3) : IsMinimalCut (G m) (T f) :=
  ⟨not_pre f, pre f⟩

lemma T_inj : Function.Injective (T (m := m)) := by
  intro f g hfg
  funext j
  have hb : 2 + 3 * j.1 + (f j).1 < 3 * m + 2 := by have := j.2; have := (f j).2; omega
  have mem : (⟨2 + 3 * j.1 + (f j).1, hb⟩ : Fin (3 * m + 2)) ∈ T f := by
    change 2 ≤ 2 + 3 * j.1 + (f j).1 ∧
      (2 + 3 * j.1 + (f j).1 - 2) % 3 = F f ((2 + 3 * j.1 + (f j).1 - 2) / 3)
    have q : (2 + 3 * j.1 + (f j).1 - 2) / 3 = j.1 := by have := (f j).2; omega
    rw [q, F_eq]
    have := (f j).2
    omega
  rw [hfg] at mem
  change 2 ≤ 2 + 3 * j.1 + (f j).1 ∧
    (2 + 3 * j.1 + (f j).1 - 2) % 3 = F g ((2 + 3 * j.1 + (f j).1 - 2) / 3) at mem
  have q : (2 + 3 * j.1 + (f j).1 - 2) / 3 = j.1 := by have := (f j).2; omega
  rw [q, F_eq] at mem
  apply Fin.ext
  have := (f j).2
  omega

end Sy

theorem erdos_150.variants.seymour (m : ℕ) : 3 ^ m ≤ maxMinimalCuts (3 * m + 2) := by
  classical
  have hsub : Set.range (Sy.T (m := m)) ⊆ {T | IsMinimalCut (Sy.G m) T} := by
    rintro _ ⟨f, rfl⟩
    exact Sy.isMin f
  have h1 : (Set.range (Sy.T (m := m))).ncard = 3 ^ m := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sy.T_inj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hb : BddAbove {k | ∃ G : SimpleGraph (Fin (3 * m + 2)),
      {T : Set (Fin (3 * m + 2)) | IsMinimalCut G T}.ncard = k} := by
    refine ⟨(Set.univ : Set (Set (Fin (3 * m + 2)))).ncard, ?_⟩
    rintro k ⟨G, rfl⟩
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have h3 := le_csSup hb ⟨Sy.G m, rfl⟩
  unfold maxMinimalCuts
  omega

end Erdos150

#print axioms Erdos150.erdos_150.variants.seymour
