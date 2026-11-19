import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

open Filter Finset

namespace Erdos1033

namespace EL

/-- Vertices `[0,h)` = A₁, `[h,2h)` = A₂, `[2h,∞)` = B. Complete between A and B, and
a `d`-regular circulant bipartite graph between A₁ and A₂. -/
def adj (h d x y : ℕ) : Prop :=
  (x < 2 * h ∧ 2 * h ≤ y) ∨ (2 * h ≤ x ∧ y < 2 * h) ∨
    (x < h ∧ h ≤ y ∧ y < 2 * h ∧ (x + y) % h < d) ∨
    (h ≤ x ∧ x < 2 * h ∧ y < h ∧ (x + y) % h < d)

lemma adj_symm (h d x y : ℕ) (hxy : adj h d x y) : adj h d y x := by
  unfold adj at *
  rw [Nat.add_comm y x]
  omega

def G (n h d : ℕ) : SimpleGraph (Fin n) where
  Adj x y := adj h d x.val y.val
  symm := ⟨fun x y hxy => adj_symm h d _ _ hxy⟩
  loopless := ⟨fun x hx => by unfold adj at hx; omega⟩

lemma cardFin (n : ℕ) (p : ℕ → Prop) [DecidablePred p]
    [DecidablePred (fun w : Fin n => p w.val)] :
    #(univ.filter (fun w : Fin n => p w.val)) = #((range n).filter p) := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
    mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.isLt, hw⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

lemma inj (h v m : ℕ) :
    Set.InjOn (fun y => (v + y) % h) (Ico m (m + h) : Set ℕ) := by
  intro y hy y' hy' hyy
  simp only [coe_Ico, Set.mem_Ico] at hy hy'
  have hmod : y ≡ y' [MOD h] := Nat.ModEq.add_left_cancel' v hyy
  rcases le_total y y' with hle | hle
  · have hd := (Nat.modEq_iff_dvd' hle).mp hmod
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

lemma count (h d v m : ℕ) (hd : d ≤ h) :
    #((Ico m (m + h)).filter (fun y => (v + y) % h < d)) = d := by
  set s := Ico m (m + h)
  have hinj := inj h v m
  have himg : s.image (fun y => (v + y) % h) = range h := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [mem_range]
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · exfalso
        simp only [s, mem_Ico] at hy
        omega
      · exact Nat.mod_lt _ h0
    · rw [card_image_of_injOn hinj]
      simp only [card_range, Nat.card_Ico]
      omega
  calc #(s.filter (fun y => (v + y) % h < d))
      = #((s.filter (fun y => (v + y) % h < d)).image (fun y => (v + y) % h)) :=
        (card_image_of_injOn (hinj.mono (coe_subset.mpr (filter_subset _ _)))).symm
    _ = #((s.image (fun y => (v + y) % h)).filter (· < d)) := by
        congr 1
        ext z
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, hd⟩
        · rintro ⟨⟨y, hy, rfl⟩, hd⟩
          exact ⟨y, ⟨hy, hd⟩, rfl⟩
    _ = #((range h).filter (· < d)) := by rw [himg]
    _ = d := by
        have : (range h).filter (· < d) = range d := by
          ext z; simp only [mem_filter, mem_range]; omega
        rw [this, card_range]

lemma degNat (n h d v : ℕ) (hd : d ≤ h) (hn : 2 * h ≤ n) [DecidablePred (adj h d v)] :
    #((range n).filter (adj h d v)) = if v < 2 * h then n - 2 * h + d else 2 * h := by
  split_ifs with hv
  · by_cases hv1 : v < h
    · have : (range n).filter (adj h d v) =
          Ico (2 * h) n ∪ (Ico h (h + h)).filter (fun y => (v + y) % h < d) := by
        ext y; simp only [mem_filter, mem_range, mem_union, mem_Ico, adj]; omega
      rw [this, card_union_of_disjoint, Nat.card_Ico, count h d v h hd]
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [mem_filter, mem_Ico] at hy hy'
      omega
    · have : (range n).filter (adj h d v) =
          Ico (2 * h) n ∪ (Ico 0 (0 + h)).filter (fun y => (v + y) % h < d) := by
        ext y; simp only [mem_filter, mem_range, mem_union, mem_Ico, adj]; omega
      rw [this, card_union_of_disjoint, Nat.card_Ico, count h d v 0 hd]
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [mem_filter, mem_Ico] at hy hy'
      omega
  · have : (range n).filter (adj h d v) = range (2 * h) := by
      ext y; simp only [mem_filter, mem_range, adj]; omega
    rw [this, card_range]

lemma deg (n h d : ℕ) (hd : d ≤ h) (hn : 2 * h ≤ n) [DecidableRel (G n h d).Adj]
    (v : Fin n) :
    (G n h d).degree v = if v.val < 2 * h then n - 2 * h + d else 2 * h := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  rw [← degNat n h d v.val hd hn, ← cardFin n (adj h d v.val)]
  congr 1
  ext w
  rw [mem_filter, mem_filter]
  rfl

lemma edges (n h d : ℕ) (hd : d ≤ h) (hn : 2 * h ≤ n) [DecidableRel (G n h d).Adj] :
    2 * #(G n h d).edgeFinset = 2 * h * (n - 2 * h + d) + (n - 2 * h) * (2 * h) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [deg n h d hd hn]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < 2 * h then n - 2 * h + d else 2 * h) n,
    range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 * h)) hn]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (by simp only [mem_Ico] at hk; omega)),
    Finset.sum_congr rfl (fun k hk => if_neg (by simp only [mem_Ico] at hk; omega))]
  simp only [sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero]

lemma three (h d x y z : ℕ) (h1 : adj h d x y) (h2 : adj h d x z) (h3 : adj h d y z) :
    (2 * h ≤ x ∧ y < 2 * h ∧ z < 2 * h) ∨ (x < 2 * h ∧ 2 * h ≤ y ∧ z < 2 * h) ∨
      (x < 2 * h ∧ y < 2 * h ∧ 2 * h ≤ z) := by
  unfold adj at h1 h2 h3
  rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 | h3 <;> omega

lemma tri (n h d : ℕ) (hd : d ≤ h) (hn : 2 * h ≤ n) [DecidableRel (G n h d).Adj]
    (t : Finset (Fin n)) (ht : (G n h d).IsNClique 3 t) :
    ∑ v ∈ t, (G n h d).degree v ≤ 2 * (n - 2 * h + d) + 2 * h := by
  obtain ⟨a, b, c, h1, h2, h3, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hab : a ≠ b := (G n h d).ne_of_adj h1
  have hac : a ≠ c := (G n h d).ne_of_adj h2
  have hbc : b ≠ c := (G n h d).ne_of_adj h3
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  rw [deg n h d hd hn, deg n h d hd hn, deg n h d hd hn]
  change adj h d a.val b.val at h1
  change adj h d a.val c.val at h2
  change adj h d b.val c.val at h3
  rcases three h d _ _ _ h1 h2 h3 with ⟨p, q, r⟩ | ⟨p, q, r⟩ | ⟨p, q, r⟩
  · rw [if_neg (by omega), if_pos q, if_pos r]; omega
  · rw [if_pos p, if_neg (by omega), if_pos r]; omega
  · rw [if_pos p, if_pos q, if_neg (by omega)]; omega

end EL

open scoped Classical in
theorem erdos_1033.variants.erdos_laskar :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), n ^ 2 < 4 * #G.edgeFinset ∧
      ∀ t, G.IsNClique 3 t → ∑ v ∈ t, (G.degree v : ℝ) ≤ 2 * (Real.sqrt 3 - 1) * n + C := by
  set s := Real.sqrt 3 with hs_def
  have hs2 : s * s = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hslo : 1.732 < s := by nlinarith
  have hshi : s < 1.7321 := by nlinarith
  refine ⟨6, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨100, fun n hn => ?_⟩
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := n / (2 * s) with hx_def
  have hx : (n : ℝ) = 2 * (s * x) := by rw [hx_def]; field_simp
  have hx0 : 0 ≤ x := by rw [hx_def]; positivity
  have hsx1 : 1.732 * x ≤ s * x := mul_le_mul_of_nonneg_right hslo.le hx0
  have hsx2 : s * x ≤ 1.7321 * x := mul_le_mul_of_nonneg_right hshi.le hx0
  have hxbig : 28 ≤ x := by linarith
  set r : ℝ := (7 * s / 6 - 2) * n with hr_def
  have hr : r = 7 * x - 4 * (s * x) := by
    rw [hr_def, hx]; linear_combination (7 / 3 * x) * hs2
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set h := ⌊x⌋₊ with hh
  set d := ⌈r⌉₊ + 1 with hd_def
  have hh1 : (h : ℝ) ≤ x := Nat.floor_le hx0
  have hh2 : x < h + 1 := Nat.lt_floor_add_one x
  have hd1 : r + 1 ≤ (d : ℝ) := by
    rw [hd_def]; push_cast; linarith [Nat.le_ceil r]
  have hd2 : (d : ℝ) < r + 2 := by
    rw [hd_def]; push_cast; linarith [Nat.ceil_lt_add_one hr0]
  have hdh : d ≤ h := by
    have : (d : ℝ) ≤ h := by linarith
    exact_mod_cast this
  have h2n : 2 * h ≤ n := by
    have : ((2 * h : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  refine ⟨EL.G n h d, ?_, ?_⟩
  · have he : 2 * #(EL.G n h d).edgeFinset =
        2 * h * (n - 2 * h + d) + (n - 2 * h) * (2 * h) := by
      convert EL.edges n h d hdh h2n
    have key : (n : ℝ) ^ 2 < 2 * ((2 * h * (n - 2 * h + d) + (n - 2 * h) * (2 * h) : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_add,
        Nat.cast_sub h2n]
      push_cast
      have eA : 0 ≤ (x - h) * (2 * h + 2 * x - n) := mul_nonneg (by linarith) (by linarith)
      have eB : (x - 1) * (r + 1) ≤ (h : ℝ) * d :=
        mul_le_mul (by linarith) hd1 (by linarith) (Nat.cast_nonneg h)
      have eC : 8 * x * n - 16 * x ^ 2 + 4 * x * r - (n : ℝ) ^ 2 = 0 := by
        rw [hx, hr]; linear_combination (-4 * x ^ 2) * hs2
      linarith [eA, eB, eC, hsx1, hr, hxbig]
    have key' : n ^ 2 < 2 * (2 * h * (n - 2 * h + d) + (n - 2 * h) * (2 * h)) := by
      exact_mod_cast key
    rw [← he] at key'
    linarith
  · intro t ht
    have htri := EL.tri n h d hdh h2n t ht
    have h' : ((∑ v ∈ t, (EL.G n h d).degree v : ℕ) : ℝ) ≤
        ((2 * (n - 2 * h + d) + 2 * h : ℕ) : ℝ) := by exact_mod_cast htri
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_sub h2n] at h'
    push_cast at h'
    have hsn : s * n = 6 * x := by rw [hx]; linear_combination (2 * x) * hs2
    linarith [hsn, hh2, hd2, hr, hx, h']

end Erdos1033

#print axioms Erdos1033.erdos_1033.variants.erdos_laskar
