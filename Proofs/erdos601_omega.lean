import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Nth
import Mathlib.Order.OrderIsoNat

open Cardinal Ordinal SimpleGraph

namespace Erdos601

universe u

def HasPathOrIndepSetOfType (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    (∃ f : ℕ → α.ToType, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
    (∃ s : Set α.ToType, G.IsIndepSet s ∧ typeLT s = α)

namespace R

variable (G : SimpleGraph ℕ)

open Classical in
/-- One Ramsey step: keep the neighbours of the minimum if there are infinitely many,
otherwise keep the non-neighbours; always drop the minimum. -/
noncomputable def next (S : Set ℕ) : Set ℕ :=
  if (S ∩ G.neighborSet (sInf S)).Infinite then ((S ∩ G.neighborSet (sInf S)) \ {sInf S})
  else ((S \ G.neighborSet (sInf S)) \ {sInf S})

lemma next_inf (S : Set ℕ) (hS : S.Infinite) : (next G S).Infinite := by
  unfold next
  split_ifs with h
  · exact h.sdiff (Set.finite_singleton _)
  · have hfin : (S ∩ G.neighborSet (sInf S)).Finite := Set.not_infinite.1 h
    have : (S \ G.neighborSet (sInf S)).Infinite := by
      intro hf
      refine hS ((hf.union hfin).subset fun y hy => ?_)
      by_cases hy' : y ∈ G.neighborSet (sInf S)
      · exact Or.inr ⟨hy, hy'⟩
      · exact Or.inl ⟨hy, hy'⟩
    exact this.sdiff (Set.finite_singleton _)

lemma next_sub (S : Set ℕ) : next G S ⊆ S \ {sInf S} := by
  unfold next
  split_ifs with h
  · intro y hy; exact ⟨hy.1.1, hy.2⟩
  · intro y hy; exact ⟨hy.1.1, hy.2⟩

lemma next_adj (S : Set ℕ) (h : (S ∩ G.neighborSet (sInf S)).Infinite) :
    ∀ y ∈ next G S, G.Adj (sInf S) y := by
  intro y hy
  unfold next at hy
  rw [if_pos h] at hy
  exact hy.1.2

lemma next_nadj (S : Set ℕ) (h : ¬ (S ∩ G.neighborSet (sInf S)).Infinite) :
    ∀ y ∈ next G S, ¬ G.Adj (sInf S) y := by
  intro y hy
  unfold next at hy
  rw [if_neg h] at hy
  exact hy.1.2

noncomputable def seq : ℕ → {S : Set ℕ // S.Infinite}
  | 0 => ⟨Set.univ, Set.infinite_univ⟩
  | n + 1 => ⟨next G (seq n).1, next_inf G _ (seq n).2⟩

noncomputable def x (n : ℕ) : ℕ := sInf (seq G n).1

def c (n : ℕ) : Prop := ((seq G n).1 ∩ G.neighborSet (x G n)).Infinite

lemma x_mem (n : ℕ) : x G n ∈ (seq G n).1 := Nat.sInf_mem (seq G n).2.nonempty

lemma seq_succ (n : ℕ) : (seq G (n + 1)).1 = next G (seq G n).1 := rfl

lemma seq_anti (i : ℕ) : ∀ k, (seq G (i + k)).1 ⊆ (seq G i).1
  | 0 => le_rfl
  | k + 1 => by
    intro y hy
    rw [← add_assoc, seq_succ] at hy
    exact seq_anti i k (next_sub G _ hy).1

lemma later_mem (i j : ℕ) (h : i < j) : x G j ∈ (seq G (i + 1)).1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact seq_anti G (i + 1) k (x_mem G _)

lemma x_lt (i j : ℕ) (h : i < j) : x G i < x G j := by
  have h1 := next_sub G _ (later_mem G i j h)
  have h2 : x G i ≤ x G j := Nat.sInf_le h1.1
  exact lt_of_le_of_ne h2 (fun e => h1.2 e.symm)

lemma adj_of (i j : ℕ) (h : i < j) (hc : c G i) : G.Adj (x G i) (x G j) :=
  next_adj G _ hc _ (later_mem G i j h)

lemma nadj_of (i j : ℕ) (h : i < j) (hc : ¬ c G i) : ¬ G.Adj (x G i) (x G j) :=
  next_nadj G _ hc _ (later_mem G i j h)

theorem ramsey_nat :
    (∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, G.Adj (f n) (f (n + 1))) ∨
      ∃ s : Set ℕ, s.Infinite ∧ G.IsIndepSet s := by
  classical
  by_cases hinf : {i | c G i}.Infinite
  · left
    refine ⟨fun n => x G (Nat.nth (c G) n), ?_, ?_⟩
    · intro a b hab
      exact x_lt G _ _ (Nat.nth_strictMono hinf hab)
    · intro n
      exact adj_of G _ _ (Nat.nth_strictMono hinf (Nat.lt_succ_self n))
        (Nat.nth_mem_of_infinite hinf n)
  · right
    have hfin : {i | c G i}.Finite := Set.not_infinite.1 hinf
    obtain ⟨N, hN⟩ := hfin.bddAbove
    have hnc : ∀ i, N + 1 ≤ i → ¬ c G i := fun i hi hc => by
      have := hN hc
      omega
    refine ⟨Set.range (fun k => x G (N + 1 + k)), ?_, ?_⟩
    · apply Set.infinite_range_of_injective
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (x_lt G (N + 1 + a) (N + 1 + b) (by omega)).ne hab
      · exact (x_lt G (N + 1 + b) (N + 1 + a) (by omega)).ne hab.symm
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
      have hab : a ≠ b := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hab with h | h
      · exact nadj_of G _ _ (by omega) (hnc _ (by omega))
      · intro hadj
        exact nadj_of G _ _ (by omega) (hnc _ (by omega)) (G.adj_symm hadj)

end R

universe v

/-- Order types are invariant under images along an order isomorphism, across universes. -/
theorem typeLT_image {X : Type u} {Y : Type v} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (e : X ≃o Y) (A : Set X) :
    Ordinal.lift.{v} (typeLT A) = Ordinal.lift.{u} (typeLT (e '' A)) := by
  let f : A ≃ (e '' A) := e.toEquiv.image A
  have g : ((· < ·) : A → A → Prop) ≃r ((· < ·) : (e '' A) → (e '' A) → Prop) :=
    ⟨f, fun {a b} => by
      show e a.1 < e b.1 ↔ a.1 < b.1
      exact e.lt_iff_lt⟩
  exact g.ordinal_lift_type_eq

theorem at_omega_gen : HasPathOrIndepSetOfType.{u} ω := by
  intro G
  have key : Ordinal.lift.{u} (typeLT ℕ) =
      Ordinal.lift.{0} (typeLT (ω : Ordinal.{u}).ToType) := by
    rw [Ordinal.type_nat_lt, Ordinal.type_toType]
    simp
  obtain ⟨e₀⟩ := Ordinal.lift_type_eq.{0, u, 0}.mp key
  let e : ℕ ≃o (ω : Ordinal.{u}).ToType := OrderIso.ofRelIsoLT e₀
  rcases R.ramsey_nat (SimpleGraph.comap (fun n => e n) G) with ⟨f, hf, hadj⟩ | ⟨s, hs, hind⟩
  · left
    exact ⟨fun n => e (f n), e.injective.comp hf.injective, fun n => hadj n⟩
  · right
    refine ⟨e '' s, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
      exact hind ha hb (fun h => hne (by rw [h]))
    · have : Infinite s := hs.to_subtype
      have h1 : typeLT s = ω := by
        rw [← Ordinal.type_nat_lt]
        exact Ordinal.type_eq.2 ⟨(Nat.Subtype.orderIsoOfNat s).symm.toRelIsoLT⟩
      have h2 := typeLT_image e s
      rw [h1] at h2
      simpa using h2.symm

namespace erdos_601.variants

theorem at_omega : HasPathOrIndepSetOfType ω := at_omega_gen

end erdos_601.variants

end Erdos601

#print axioms Erdos601.erdos_601.variants.at_omega
