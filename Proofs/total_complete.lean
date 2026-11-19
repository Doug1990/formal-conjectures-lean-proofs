import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

/-! Local restatement of FormalConjecturesForMathlib/Combinatorics/SimpleGraph/TotalColouring.lean
(definitions copied verbatim). -/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def IsTotalColoring {ι : Type*} (c : V ⊕ G.edgeSet → ι) : Prop :=
  (∀ u v, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → (∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
    c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → c (Sum.inl v) ≠ c (Sum.inr e))

def TotalColorable (n : ℕ) : Prop :=
  ∃ c : V ⊕ G.edgeSet → Fin n, G.IsTotalColoring c

noncomputable def totalChromaticNumber : ℕ :=
  sInf {n | G.TotalColorable n}

end SimpleGraph

open SimpleGraph

namespace TotalColoringConjecture

lemma mod2 {x m : ℕ} (h : x < 2 * m) : x % m = if x < m then x else x - m := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Sum of the two endpoints of an edge. -/
def esum {n : ℕ} : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun i j => i.val + j.val, fun _ _ => Nat.add_comm _ _⟩

lemma esum_mk {n : ℕ} (i j : Fin n) : esum s(i, j) = i.val + j.val := rfl

lemma decomp {n : ℕ} (e : (completeGraph (Fin n)).edgeSet) (v : Fin n)
    (hv : v ∈ (e : Sym2 (Fin n))) : ∃ a : Fin n, (e : Sym2 (Fin n)) = s(v, a) ∧ v ≠ a := by
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 hv
  refine ⟨a, ha, ?_⟩
  have he := e.2
  rw [ha, mem_edgeSet] at he
  exact he

lemma colorable (n : ℕ) :
    (completeGraph (Fin n)).TotalColorable (2 * (n / 2) + 1) := by
  set m := 2 * (n / 2) + 1 with hm
  have hnm : n ≤ m := by omega
  refine ⟨Sum.elim (fun i : Fin n => (⟨(2 * i.val) % m, Nat.mod_lt _ (by omega)⟩ : Fin m))
    (fun e : (completeGraph (Fin n)).edgeSet =>
      (⟨esum (e : Sym2 (Fin n)) % m, Nat.mod_lt _ (by omega)⟩ : Fin m)), ?_, ?_, ?_⟩
  · intro u v huv h
    simp only [Sum.elim_inl, Fin.mk.injEq] at h
    have hu := u.2
    have hv := v.2
    have hne : u.val ≠ v.val := fun h' => huv (Fin.ext h')
    rw [mod2 (by omega), mod2 (by omega)] at h
    split_ifs at h <;> omega
  · intro e f hef ⟨v, hve, hvf⟩ h
    obtain ⟨a, hea, hva⟩ := decomp e v hve
    obtain ⟨b, hfb, hvb⟩ := decomp f v hvf
    simp only [Sum.elim_inr, Fin.mk.injEq] at h
    rw [hea, hfb, esum_mk, esum_mk] at h
    have := v.2
    have := a.2
    have := b.2
    rw [mod2 (by omega), mod2 (by omega)] at h
    have hab : a = b := by
      apply Fin.ext
      split_ifs at h <;> omega
    apply hef
    apply Subtype.ext
    rw [hea, hfb, hab]
  · intro v e hve h
    obtain ⟨a, hea, hva⟩ := decomp e v hve
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    rw [hea, esum_mk] at h
    have := v.2
    have := a.2
    have hne : v.val ≠ a.val := fun h' => hva (Fin.ext h')
    rw [mod2 (by omega), mod2 (by omega)] at h
    split_ifs at h <;> omega

theorem total_coloring_conjecture.variants.complete_graph (n : ℕ) :
    (completeGraph (Fin n)).totalChromaticNumber ≤ (completeGraph (Fin n)).maxDegree + 2 := by
  have h2 : (completeGraph (Fin n)).totalChromaticNumber ≤ 2 * (n / 2) + 1 :=
    Nat.sInf_le (colorable n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · omega
  · have := (completeGraph (Fin n)).degree_le_maxDegree ⟨0, hn⟩
    rw [complete_graph_degree, Fintype.card_fin] at this
    omega

end TotalColoringConjecture

#print axioms TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph
