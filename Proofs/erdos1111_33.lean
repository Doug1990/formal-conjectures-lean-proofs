import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace Erdos1111

/-- Restated from the checkout (ErdosProblems/1111.lean). -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

namespace TT

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Parity of a walk inside `A` against a 2-colouring of `A`. -/
theorem par (A : Set V) (f : V → Bool) (hf : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y) :
    ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, x ∈ A) → (Even p.length ↔ f u = f v) := by
  intro u v p
  induction p with
  | nil => intro _; simp
  | @cons a b c hab q ih =>
    intro h
    have hq : ∀ x ∈ q.support, x ∈ A := fun x hx => h x (by simp [hx])
    have hne := hf a (h a (by simp)) b (hq b q.start_mem_support) hab
    rw [Walk.length_cons, Nat.even_add_one, ih hq]
    revert hne
    cases f a <;> cases f b <;> cases f c <;> simp

/-- A set containing an odd closed walk has chromatic number at least 3. -/
theorem three_le (A : Set V) {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hA : ∀ x ∈ p.support, x ∈ A) : 3 ≤ (G.induce A).chromaticNumber := by
  classical
  by_contra h
  have h' : (G.induce A).chromaticNumber ≤ 2 := Order.le_of_lt_add_one (not_le.mp h)
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp h'
  let f : V → Bool := fun x => if hx : x ∈ A then decide (c ⟨x, hx⟩ = 0) else false
  have hf : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y := by
    intro x hx y hy hxy
    have hv := c.valid (show (G.induce A).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    simp only [f, dif_pos hx, dif_pos hy]
    revert hv
    generalize c ⟨x, hx⟩ = a
    generalize c ⟨y, hy⟩ = b
    intro hv
    fin_cases a <;> fin_cases b <;> simp_all
  exact (Nat.not_even_iff_odd.mpr hodd) ((par A f hf p hA).mpr rfl)

end TT

open SimpleGraph in
theorem erdos_1111.variants.three_three :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      8 ≤ G.chromaticNumber → G.CliqueFree 3 →
        ∃ A B : Set V, Anticomplete G A B ∧
          3 ≤ (G.induce A).chromaticNumber ∧ 3 ≤ (G.induce B).chromaticNumber := by
  intro V _ G hχ hG
  classical
  have hnc : ¬ G.Colorable 2 := by
    intro h
    have h1 := hχ.trans h.chromaticNumber_le
    exact absurd (by exact_mod_cast h1 : (8 : ℕ) ≤ 2) (by decide)
  rw [two_colorable_iff_forall_loop_even] at hnc
  have hex : ∃ m, Odd m ∧ ∃ u, ∃ p : G.Walk u u, p.length = m := by
    by_contra hcon
    apply hnc
    intro u p
    by_contra hp
    exact hcon ⟨p.length, Nat.not_even_iff_odd.mp hp, u, p, rfl⟩
  obtain ⟨hkodd, u, C, hCk⟩ := Nat.find_spec hex
  have hmin : ∀ v (p : G.Walk v v), Odd p.length → Nat.find hex ≤ p.length := fun v p hp =>
    Nat.find_min' hex ⟨hp, v, p, rfl⟩
  generalize Nat.find hex = k at hkodd hCk hmin
  subst hCk
  have hadj : ∀ i < C.length, G.Adj (C.getVert i) (C.getVert (i + 1)) :=
    fun i hi => C.adj_getVert_succ hi
  have hend : C.getVert C.length = C.getVert 0 := by rw [C.getVert_length, C.getVert_zero]
  have hk5 : 5 ≤ C.length := by
    have hodd' := Nat.odd_iff.mp hkodd
    by_contra hlt
    have h13 : C.length = 1 ∨ C.length = 3 := by omega
    rcases h13 with h1 | h3
    · have h01 := hadj 0 (by omega)
      have hv : C.getVert (0 + 1) = C.getVert 0 := by rw [show 0 + 1 = C.length by omega, hend]
      rw [hv] at h01
      exact h01.ne rfl
    · have h01 := hadj 0 (by omega)
      have h12 := hadj 1 (by omega)
      have h20 := hadj 2 (by omega)
      have hv : C.getVert (2 + 1) = C.getVert 0 := by rw [show 2 + 1 = C.length by omega, hend]
      rw [hv] at h20
      exact hG {C.getVert 0, C.getVert (0 + 1), C.getVert (1 + 1)}
        (is3Clique_triple_iff.mpr ⟨h01, h20.symm, h12⟩)
  have hnorm : ∀ i ≤ C.length, ∃ j < C.length, C.getVert j = C.getVert i := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · exact ⟨i, h, rfl⟩
    · exact ⟨0, by omega, by rw [h, hend]⟩
  let P : V → Prop := fun x => ∃ i, i < C.length ∧ G.Adj (C.getVert i) x
  let A : Set V := {x | x ∈ C.support}
  have hAmem : ∀ x ∈ A, ∃ j < C.length, C.getVert j = x := by
    intro x hx
    obtain ⟨n, hn, hle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    obtain ⟨j, hj, hje⟩ := hnorm n hle
    exact ⟨j, hj, hje.trans hn⟩
  have hAX : ∀ x ∈ A, P x := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hAmem x hx
    obtain ⟨j', hj', hje⟩ := hnorm (j + 1) (by omega)
    exact ⟨j', hj', by rw [hje]; exact (hadj j hj).symm⟩
  -- closed walk through a, x, y, b
  have walk3 : ∀ a b x y, a ≤ b → b < C.length → G.Adj (C.getVert a) x →
      G.Adj (C.getVert b) y → G.Adj x y → (b - a) % 2 = 0 → b - a + 3 < C.length → False := by
    intro a b x y hab hb hx hy hxy hev hlt
    have e : (C.drop a).getVert (b - a) = C.getVert b := by
      rw [Walk.drop_getVert]; congr 1; omega
    have hy' : G.Adj ((C.drop a).getVert (b - a)) y := by rw [e]; exact hy
    let W : G.Walk (C.getVert a) (C.getVert a) :=
      ((C.drop a).take (b - a)).append
        (Walk.cons hy' (Walk.cons hxy.symm (Walk.cons hx.symm Walk.nil)))
    have hlen : W.length = b - a + 3 := by
      simp only [W, Walk.length_append, Walk.take_length, Walk.drop_length, Walk.length_cons,
        Walk.length_nil]
      rw [inf_eq_left.mpr (by omega : b - a ≤ C.length - a)]
    have := hmin _ W (by rw [hlen]; exact Nat.odd_iff.mpr (by omega))
    omega
  let cl : ℕ → ℕ := fun i => if i + 4 ≤ C.length then i % 2 else i + 5 - C.length
  have hcl : ∀ i < C.length, cl i ≤ 4 := by
    intro i hi
    simp only [cl]
    split_ifs <;> omega
  have key : ∀ a b x y, a < C.length → b < C.length → G.Adj (C.getVert a) x →
      G.Adj (C.getVert b) y → G.Adj x y → cl a = cl b → False := by
    intro a b x y ha hb hx hy hxy hcl'
    simp only [cl] at hcl'
    rcases le_total a b with h | h
    · exact walk3 a b x y h hb hx hy hxy (by split_ifs at hcl' <;> omega)
        (by split_ifs at hcl' <;> omega)
    · exact walk3 b a y x h ha hy hx hxy.symm (by split_ifs at hcl' <;> omega)
        (by split_ifs at hcl' <;> omega)
  refine ⟨A, {x | ¬ P x}, ⟨?_, ?_⟩, TT.three_le A C hkodd (fun x hx => hx), ?_⟩
  · exact Set.disjoint_left.mpr fun x hx hxB => hxB (hAX x hx)
  · intro a ha b hb hab
    obtain ⟨j, hj, rfl⟩ := hAmem a ha
    exact hb ⟨j, hj, hab⟩
  · by_contra h
    have h' : (G.induce {x | ¬ P x}).chromaticNumber ≤ 2 :=
      Order.le_of_lt_add_one (not_le.mp h)
    obtain ⟨cB⟩ : (G.induce {x | ¬ P x}).Colorable 2 :=
      chromaticNumber_le_iff_colorable.mp (by exact_mod_cast h')
    let f : V → Fin 7 := fun x =>
      if hx : P x then
        ⟨cl (Classical.choose hx), by have := hcl _ (Classical.choose_spec hx).1; omega⟩
      else ⟨5 + (cB ⟨x, hx⟩).val, by have := (cB ⟨x, hx⟩).isLt; omega⟩
    have hval : ∀ x y, G.Adj x y → f x ≠ f y := by
      intro x y hxy hfe
      by_cases hx : P x <;> by_cases hy : P y
      · simp only [f, dif_pos hx, dif_pos hy, Fin.mk.injEq] at hfe
        exact key _ _ x y (Classical.choose_spec hx).1 (Classical.choose_spec hy).1
          (Classical.choose_spec hx).2 (Classical.choose_spec hy).2 hxy hfe
      · simp only [f, dif_pos hx, dif_neg hy, Fin.mk.injEq] at hfe
        have := hcl _ (Classical.choose_spec hx).1
        omega
      · simp only [f, dif_neg hx, dif_pos hy, Fin.mk.injEq] at hfe
        have := hcl _ (Classical.choose_spec hy).1
        omega
      · simp only [f, dif_neg hx, dif_neg hy, Fin.mk.injEq] at hfe
        exact cB.valid (show (G.induce {x | ¬ P x}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
          (Fin.ext (by omega))
    have hcol : G.Colorable 7 := ⟨Coloring.mk f (fun h => hval _ _ h)⟩
    have h1 := hχ.trans hcol.chromaticNumber_le
    exact absurd (by exact_mod_cast h1 : (8 : ℕ) ≤ 7) (by decide)

end Erdos1111

#print axioms Erdos1111.erdos_1111.variants.three_three
