import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

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

open SimpleGraph

/-- Degrees of a graph whose edges are the pairs of a 2-uniform family. -/
lemma deg_eq {n : ℕ} (H : Finset (Finset (Fin n)))
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ H) (v : Fin n) :
    G.degree v = (H.filter (v ∈ ·)).card := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  apply Finset.card_bij (fun w _ ↦ ({v, w} : Finset (Fin n)))
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨((hG v w).1 hw.2).2, Finset.mem_insert_self _ _⟩
  · intro w1 hw1 w2 hw2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have h1 : w1 ∈ ({v, w2} : Finset (Fin n)) := by rw [← h]; simp
    rcases Finset.mem_insert.1 h1 with h1 | h1
    · exact absurd h1.symm (G.ne_of_adj hw1)
    · exact Finset.mem_singleton.1 h1
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heH, hv⟩ := he
    have hc := (Finset.mem_powersetCard.1 (hH heH)).2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨b, by simp [(hG _ _).2 ⟨hab, heH⟩], rfl⟩
    · rw [Finset.mem_singleton] at hv
      subst hv
      refine ⟨a, ?_, Finset.pair_comm _ _⟩
      rw [Finset.pair_comm] at heH
      simp [(hG _ _).2 ⟨hab.symm, heH⟩]

lemma card_eq {n : ℕ} (H : Finset (Finset (Fin n)))
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ H) :
    G.edgeFinset.card = H.card := by
  have h2 := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ ↦ deg_eq H hH G hG v)] at h2
  have h3 : ∑ v, (H.filter (v ∈ ·)).card = 2 * H.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ e ∈ H, (∑ v : Fin n, if v ∈ e then 1 else 0) = 2 := by
      intro e he
      rw [← Finset.card_filter]
      have : (Finset.univ.filter (fun v : Fin n ↦ v ∈ e)) = e := by ext x; simp
      rw [this, (Finset.mem_powersetCard.1 (hH he)).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  omega

lemma ex_eq (n r : ℕ) (hr : 0 < r) :
    cliqueExtremalNumber n 2 (r + 1) = (turanGraph n r).edgeFinset.card := by
  classical
  apply le_antisymm
  · unfold cliqueExtremalNumber
    rcases ex_spec n 2 (fun H ↦ ¬ H.ContainsCompleteHypergraph 2 (r + 1)) with
      h0 | ⟨H, hsub, hH2, hsup⟩
    · rw [h0]; exact Nat.zero_le _
    rw [← hsup]
    let G : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b ↦ ({a, b} : Finset (Fin n)) ∈ H)
    have hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ H := by
      intro a b
      simp only [G, SimpleGraph.fromRel_adj]
      rw [Finset.pair_comm b a, or_self]
    have hcf : G.CliqueFree (r + 1) := by
      intro S hS
      apply hH2
      refine ⟨S, hS.card_eq, ?_⟩
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hT.2
      have ha : a ∈ S := hT.1 (by simp)
      have hb : b ∈ S := hT.1 (by simp)
      exact ((hG a b).1 (hS.isClique (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab)).2
    have hb := hcf.card_edgeFinset_le
    simp only [Fintype.card_fin] at hb
    rw [← card_eq H hsub G hG, card_edgeFinset_turanGraph]
    exact hb
  · let T := turanGraph n r
    let H : Finset (Finset (Fin n)) := ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
      (fun e ↦ ∀ a ∈ e, ∀ b ∈ e, a ≠ b → T.Adj a b)
    have hsub : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := Finset.filter_subset _ _
    have hG : ∀ a b, T.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ H := by
      intro a b
      constructor
      · intro h
        have hab := T.ne_of_adj h
        refine ⟨hab, Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2
          ⟨Finset.subset_univ _, Finset.card_pair hab⟩, ?_⟩⟩
        intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact h
        · exact h.symm
        · exact absurd rfl hxy
      · rintro ⟨hab, hmem⟩
        exact (Finset.mem_filter.1 hmem).2 a (by simp) b (by simp) hab
    rw [card_eq H hsub T hG]
    unfold cliqueExtremalNumber
    apply le_ex _ _ _ H hsub
    rintro ⟨S, hS, hSH⟩
    apply turanGraph_cliqueFree (n := n) hr S
    rw [isNClique_iff]
    refine ⟨?_, hS⟩
    intro a ha b hb hab
    have hmem : ({a, b} : Finset (Fin n)) ∈ H := hSH (Finset.mem_powersetCard.2
      ⟨Finset.insert_subset_iff.2 ⟨ha, Finset.singleton_subset_iff.2 hb⟩, Finset.card_pair hab⟩)
    exact (hG a b).2 ⟨hab, hmem⟩

lemma ex_up (n r : ℕ) (hr : 0 < r) :
    2 * r * cliqueExtremalNumber n 2 (r + 1) ≤ (r - 1) * n ^ 2 := by
  rw [ex_eq n r hr]
  exact mul_card_edgeFinset_turanGraph_le

lemma ex_low (n r : ℕ) (hr : 0 < r) :
    (n ^ 2 - r ^ 2) * (r - 1) ≤ 2 * r * (cliqueExtremalNumber n 2 (r + 1) + 1) := by
  rw [ex_eq n r hr, card_edgeFinset_turanGraph]
  have h1 := Nat.lt_mul_div_succ ((n ^ 2 - (n % r) ^ 2) * (r - 1)) (Nat.mul_pos two_pos hr)
  have h2 : (n ^ 2 - r ^ 2) * (r - 1) ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (Nat.pow_le_pow_left (Nat.mod_lt n hr).le 2) _)
  exact h2.trans (h1.le.trans (Nat.mul_le_mul_left _ (by omega)))

lemma ex_up_real (n r : ℕ) (hr : 0 < r) :
    2 * (r : ℝ) * cliqueExtremalNumber n 2 (r + 1) ≤ ((r : ℝ) - 1) * (n : ℝ) ^ 2 := by
  have h := ex_up n r hr
  have hc : (((2 * r * cliqueExtremalNumber n 2 (r + 1) : ℕ)) : ℝ) ≤ (((r - 1) * n ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.2 h
  push_cast [Nat.cast_sub (by omega : 1 ≤ r)] at hc
  linarith

lemma ex_low_real (n r : ℕ) (hr : 0 < r) (hn : r ≤ n) :
    ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((r : ℝ) - 1) ≤
      2 * (r : ℝ) * (cliqueExtremalNumber n 2 (r + 1) + 1) := by
  have h := ex_low n r hr
  have hc : ((((n ^ 2 - r ^ 2) * (r - 1) : ℕ)) : ℝ) ≤
      ((2 * r * (cliqueExtremalNumber n 2 (r + 1) + 1) : ℕ) : ℝ) := Nat.cast_le.2 h
  push_cast [Nat.cast_sub (Nat.pow_le_pow_left hn 2), Nat.cast_sub (by omega : 1 ≤ r)] at hc
  linarith

/-- Turán's theorem gives the graph case:
$\mathrm{ex}_2(n,K_k)/\binom{n}{2}\to 1-1/(k-1)$. -/
theorem erdos_712.variants.graph_case (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / n.choose 2)
      atTop (𝓝 (1 - 1 / ((k : ℝ) - 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 0 < r := by omega
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : ((r + 1 : ℕ) : ℝ) - 1 = r := by push_cast; ring
  rw [hk']
  have hx : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h1x : Tendsto (fun n : ℕ ↦ 1 - 1 / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hx
  have hU : Tendsto (fun n : ℕ ↦ (1 - 1 / (r : ℝ)) * (1 / (1 - 1 / (n : ℝ)))) atTop
      (𝓝 ((1 - 1 / (r : ℝ)) * (1 / (1 - 0)))) :=
    (tendsto_const_nhds.div h1x (by norm_num)).const_mul _
  have hL : Tendsto (fun n : ℕ ↦ (1 - 1 / (r : ℝ)) *
      ((1 - (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 2) / (1 - 1 / (n : ℝ))) -
        2 * (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ))) atTop
      (𝓝 ((1 - 1 / (r : ℝ)) * ((1 - (r : ℝ) ^ 2 * 0 ^ 2) / (1 - 0)) - 2 * 0 ^ 2 / (1 - 0))) :=
    (((tendsto_const_nhds.sub (tendsto_const_nhds.mul (hx.pow 2))).div h1x
      (by norm_num)).const_mul _).sub ((tendsto_const_nhds.mul (hx.pow 2)).div h1x (by norm_num))
  have e1 : (1 - 1 / (r : ℝ)) * (1 / (1 - 0)) = 1 - 1 / (r : ℝ) := by norm_num
  have e2 : (1 - 1 / (r : ℝ)) * ((1 - (r : ℝ) ^ 2 * 0 ^ 2) / (1 - 0)) - 2 * 0 ^ 2 / (1 - 0) =
      1 - 1 / (r : ℝ) := by norm_num
  rw [e1] at hU
  rw [e2] at hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · refine eventually_atTop.2 ⟨r + 2, fun n hn ↦ ?_⟩
    have hlow := ex_low_real n r hr (by omega)
    have hN : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hN0 : (n : ℝ) ≠ 0 := by linarith
    have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hR0 : (r : ℝ) ≠ 0 := by linarith
    have eq : (1 - 1 / (r : ℝ)) * ((1 - (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 2) / (1 - 1 / (n : ℝ))) -
        2 * (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ)) =
        (((r : ℝ) - 1) * ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) - 2 * r) / ((r : ℝ) * n * ((n : ℝ) - 1)) := by
      field_simp
    have hNp : (0 : ℝ) < n := by linarith
    have hN1p : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hRp : (0 : ℝ) < r := by linarith
    have hp1 : 0 < (r : ℝ) * n * ((n : ℝ) - 1) := mul_pos (mul_pos hRp hNp) hN1p
    have hp2 : 0 < (n : ℝ) * ((n : ℝ) - 1) / 2 := by have := mul_pos hNp hN1p; linarith
    show _ ≤ (cliqueExtremalNumber n 2 (r + 1) : ℝ) / (n.choose 2 : ℕ)
    rw [eq, Nat.cast_choose_two, div_le_div_iff₀ hp1 hp2]
    have hm : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hlow hm]
  · refine eventually_atTop.2 ⟨2, fun n hn ↦ ?_⟩
    have hup := ex_up_real n r hr
    have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hN0 : (n : ℝ) ≠ 0 := by linarith
    have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hR0 : (r : ℝ) ≠ 0 := by linarith
    have eq : (1 - 1 / (r : ℝ)) * (1 / (1 - 1 / (n : ℝ))) =
        ((r : ℝ) - 1) * n / ((r : ℝ) * ((n : ℝ) - 1)) := by
      field_simp
    have hNp : (0 : ℝ) < n := by linarith
    have hN1p : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hRp : (0 : ℝ) < r := by linarith
    have hp2 : 0 < (n : ℝ) * ((n : ℝ) - 1) / 2 := by have := mul_pos hNp hN1p; linarith
    have hp3 : 0 < (r : ℝ) * ((n : ℝ) - 1) := mul_pos hRp hN1p
    show (cliqueExtremalNumber n 2 (r + 1) : ℝ) / (n.choose 2 : ℕ) ≤ _
    rw [eq, Nat.cast_choose_two, div_le_div_iff₀ hp2 hp3]
    have hm : 0 ≤ (n : ℝ) - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hup hm]

/-- With denominator $n^2$, Turán's graph limit is
$\frac12(1-1/(k-1))$. The factor $\frac12$ comes from the normalization. -/
theorem erdos_712.variants.graph_case_div_sq (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 2 k : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 ((1 / 2) * (1 - 1 / ((k : ℝ) - 1)))) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 0 < r := by omega
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : ((r + 1 : ℕ) : ℝ) - 1 = r := by push_cast; ring
  rw [hk']
  have hx : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hL : Tendsto (fun n : ℕ ↦ (1 / 2) * (1 - 1 / (r : ℝ)) *
      (1 - (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 2) - (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 ((1 / 2) * (1 - 1 / (r : ℝ)) * (1 - (r : ℝ) ^ 2 * 0 ^ 2) - 0 ^ 2)) :=
    ((tendsto_const_nhds.sub (tendsto_const_nhds.mul (hx.pow 2))).const_mul _).sub (hx.pow 2)
  have e2 : (1 / 2) * (1 - 1 / (r : ℝ)) * (1 - (r : ℝ) ^ 2 * 0 ^ 2) - 0 ^ 2 =
      (1 / 2) * (1 - 1 / (r : ℝ)) := by norm_num
  rw [e2] at hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds ?_ ?_
  · refine eventually_atTop.2 ⟨r + 2, fun n hn ↦ ?_⟩
    have hlow := ex_low_real n r hr (by omega)
    have hN : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hN0 : (n : ℝ) ≠ 0 := by linarith
    have hR0 : (r : ℝ) ≠ 0 := by linarith
    have hNp : (0 : ℝ) < n := by linarith
    have hRp : (0 : ℝ) < r := by linarith
    have eq : (1 / 2) * (1 - 1 / (r : ℝ)) * (1 - (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 2) -
        (1 / (n : ℝ)) ^ 2 =
        (((r : ℝ) - 1) * ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) - 2 * r) / (2 * (r : ℝ) * (n : ℝ) ^ 2) := by
      field_simp
    have hp1 : 0 < 2 * (r : ℝ) * (n : ℝ) ^ 2 := by have := pow_pos hNp 2; nlinarith
    have hp2 : 0 < (n : ℝ) ^ 2 := pow_pos hNp 2
    rw [eq, div_le_div_iff₀ hp1 hp2]
    nlinarith [mul_le_mul_of_nonneg_right hlow hp2.le]
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hup := ex_up_real n r hr
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hNp : (0 : ℝ) < n := by linarith
    have hRp : (0 : ℝ) < r := by linarith
    have hR0 : (r : ℝ) ≠ 0 := by linarith
    have hp2 : 0 < (n : ℝ) ^ 2 := pow_pos hNp 2
    rw [div_le_iff₀ hp2]
    have eq : (1 / 2) * (1 - 1 / (r : ℝ)) * (n : ℝ) ^ 2 =
        (((r : ℝ) - 1) * (n : ℝ) ^ 2) / (2 * r) := by
      field_simp
    rw [eq, le_div_iff₀ (by linarith)]
    linarith

end Erdos712

#print axioms Erdos712.erdos_712.variants.graph_case
#print axioms Erdos712.erdos_712.variants.graph_case_div_sq
