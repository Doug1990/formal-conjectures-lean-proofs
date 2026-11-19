import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Filter
open scoped Topology

namespace Finset
variable {V : Type*}
/-- A copy of the complete `r`-uniform hypergraph on `k` vertices. -/
def ContainsCompleteHypergraph (H : Finset (Finset V)) (r k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ S.powersetCard r ⊆ H
end Finset

namespace Hypergraph
open scoped Classical in
noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card

noncomputable def cliqueExtremalNumber (n r k : ℕ) : ℕ :=
  extremalNumber n r fun H ↦ ¬ H.ContainsCompleteHypergraph r k
end Hypergraph

namespace Erdos712

open Hypergraph

/-- Delete vertex `v`: the edges of `H` avoiding `v`, relabelled to `Fin n`. -/
noncomputable def del {n : ℕ} (v : Fin (n + 1)) (H : Finset (Finset (Fin (n + 1)))) :
    Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ : Finset (Finset (Fin n))).filter (fun e ↦ e.map (Fin.succAboveEmb v) ∈ H)

lemma mem_del {n : ℕ} (v : Fin (n + 1)) (H : Finset (Finset (Fin (n + 1))))
    (e : Finset (Fin n)) : e ∈ del v H ↔ e.map (Fin.succAboveEmb v) ∈ H := by
  classical
  unfold del
  simp

lemma card_del {n : ℕ} (v : Fin (n + 1)) (H : Finset (Finset (Fin (n + 1)))) :
    (del v H).card = (H.filter (v ∉ ·)).card := by
  classical
  let φ : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
    ⟨Finset.map (Fin.succAboveEmb v), Finset.map_injective _⟩
  have : (del v H).map φ = H.filter (v ∉ ·) := by
    ext x
    simp only [Finset.mem_map, mem_del, Finset.mem_filter]
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨he, ?_⟩
      simp only [φ, Function.Embedding.coeFn_mk, Finset.mem_map, Fin.coe_succAboveEmb, not_exists,
        not_and]
      intro a _ h
      exact Fin.succAbove_ne v a h
    · rintro ⟨hx, hv⟩
      have hsub : x ⊆ (Finset.univ : Finset (Fin n)).map (Fin.succAboveEmb v) := by
        intro y hy
        have hne : y ≠ v := fun h ↦ hv (h ▸ hy)
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
        exact Finset.mem_map.2 ⟨z, Finset.mem_univ _, hz⟩
      obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      exact ⟨u, hx, rfl⟩
  rw [← this, Finset.card_map]

open scoped Classical in
lemma ex_le_choose (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) :
    extremalNumber n r P ≤ n.choose r := by
  unfold extremalNumber
  apply Finset.sup_le
  intro H hH
  have h1 : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r :=
    Finset.mem_powerset.1 (Finset.mem_filter.1 hH).1
  calc H.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard r).card := Finset.card_le_card h1
    _ = n.choose r := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma le_choose (n r k : ℕ) : cliqueExtremalNumber n r k ≤ n.choose r :=
  ex_le_choose n r _

lemma double_count {n r : ℕ} (H : Finset (Finset (Fin (n + 1))))
    (hH : H ⊆ (Finset.univ : Finset (Fin (n + 1))).powersetCard r) :
    ∑ v, (H.filter (v ∉ ·)).card = H.card * (n + 1 - r) := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ e ∈ H, (∑ v : Fin (n + 1), if v ∉ e then 1 else 0) = n + 1 - r := by
    intro e he
    have hc : e.card = r := (Finset.mem_powersetCard.1 (hH he)).2
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun v : Fin (n + 1) ↦ v ∉ e)) = eᶜ := by
      ext x; simp
    rw [this, Finset.card_compl, Fintype.card_fin, hc]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]

open scoped Classical in
lemma ex_spec (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) :
    extremalNumber n r P = 0 ∨ ∃ H, H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r ∧ P H ∧
      H.card = extremalNumber n r P := by
  unfold extremalNumber
  rcases Finset.eq_empty_or_nonempty
      (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P) with h | h
  · left; rw [h, Finset.sup_empty]; rfl
  · right
    obtain ⟨H, hH, hsup⟩ := Finset.exists_mem_eq_sup _ h Finset.card
    obtain ⟨hH1, hH2⟩ := Finset.mem_filter.1 hH
    exact ⟨H, Finset.mem_powerset.1 hH1, hH2, hsup.symm⟩

open scoped Classical in
lemma le_ex (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) (H : Finset (Finset (Fin n)))
    (h1 : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r) (h2 : P H) :
    H.card ≤ extremalNumber n r P := by
  unfold extremalNumber
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h1, h2⟩)

lemma key (n r k : ℕ) :
    cliqueExtremalNumber (n + 1) r k * (n + 1 - r) ≤ (n + 1) * cliqueExtremalNumber n r k := by
  classical
  unfold cliqueExtremalNumber
  rcases ex_spec (n + 1) r (fun H ↦ ¬ H.ContainsCompleteHypergraph r k) with h0 | ⟨H, hsub, hH2, hsup⟩
  · rw [h0]; simp
  rw [← hsup]
  have hdc := double_count H hsub
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun _ : Fin (n + 1) ↦ H.card * (n + 1 - r))
    (g := fun v ↦ (n + 1) * (H.filter (v ∉ ·)).card) Finset.univ_nonempty (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum,
        hdc])
  refine hv.trans (Nat.mul_le_mul_left _ ?_)
  rw [← card_del]
  apply le_ex
  · intro e he
    have h := hsub ((mem_del v H e).1 he)
    rw [Finset.mem_powersetCard] at h ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [← h.2, Finset.card_map]
  · rintro ⟨S, hS, hSH⟩
    apply hH2
    refine ⟨S.map (Fin.succAboveEmb v), by rw [Finset.card_map, hS], ?_⟩
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hT.1
    apply (mem_del v H u).1
    apply hSH
    rw [Finset.mem_powersetCard]
    refine ⟨hu, ?_⟩
    rw [← hT.2, Finset.card_map]

/-- The normalized extremal number. -/
noncomputable def F (r k n : ℕ) : ℝ := (cliqueExtremalNumber n r k : ℝ) / n.choose r

lemma F_nonneg (r k n : ℕ) : 0 ≤ F r k n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma F_le_one (r k n : ℕ) : F r k n ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast le_choose n r k) (Nat.cast_nonneg _)

lemma F_step (r k n : ℕ) (hn : r ≤ n) : F r k (n + 1) ≤ F r k n := by
  have hk := key n r k
  have hch := Nat.choose_mul_succ_eq n r
  have hc : 0 < n.choose r := Nat.choose_pos hn
  have hc' : 0 < (n + 1).choose r := Nat.choose_pos (by omega)
  obtain ⟨m, hm⟩ : ∃ m, n + 1 - r = m + 1 := ⟨n - r, by omega⟩
  rw [hm] at hk hch
  have h3 : cliqueExtremalNumber (n + 1) r k * n.choose r * (n + 1) ≤
      cliqueExtremalNumber n r k * (n + 1).choose r * (n + 1) := by
    calc cliqueExtremalNumber (n + 1) r k * n.choose r * (n + 1)
        = (cliqueExtremalNumber (n + 1) r k * (m + 1)) * (n + 1).choose r := by
          rw [mul_assoc, hch]; ring
      _ ≤ ((n + 1) * cliqueExtremalNumber n r k) * (n + 1).choose r :=
          Nat.mul_le_mul_right _ hk
      _ = cliqueExtremalNumber n r k * (n + 1).choose r * (n + 1) := by ring
  have h4 := Nat.le_of_mul_le_mul_right h3 (Nat.succ_pos n)
  unfold F
  rw [div_le_div_iff₀ (by exact_mod_cast hc') (by exact_mod_cast hc)]
  exact_mod_cast h4

/-- The normalized extremal numbers have a limit in $[0,1]$. This existence result does
not determine the value asked for in Erdős Problem 712. -/
theorem erdos_712.variants.limit_exists (r k : ℕ) :
    ∃ π ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r)
        atTop (𝓝 π) := by
  have hanti : Antitone (fun m ↦ F r k (m + r)) := by
    refine antitone_nat_of_succ_le (fun m ↦ ?_)
    show F r k (m + 1 + r) ≤ F r k (m + r)
    rw [add_right_comm]
    exact F_step r k _ (Nat.le_add_left r m)
  have ht := tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨m, rfl⟩; exact F_nonneg _ _ _⟩
  refine ⟨⨅ m, F r k (m + r),
    ⟨ge_of_tendsto' ht (fun m ↦ F_nonneg _ _ _), le_of_tendsto' ht (fun m ↦ F_le_one _ _ _)⟩, ?_⟩
  exact (tendsto_add_atTop_iff_nat (f := F r k) r).1 ht

end Erdos712

#print axioms Erdos712.erdos_712.variants.limit_exists
