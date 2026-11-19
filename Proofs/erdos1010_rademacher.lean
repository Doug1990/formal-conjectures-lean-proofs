import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open SimpleGraph Finset

namespace Rad

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def A (v u : V) : ℕ := if G.Adj v u then 1 else 0

def deg (S : Finset V) (v : V) : ℕ := ∑ u ∈ S, A G v u

def P (S : Finset V) : ℕ := ∑ v ∈ S, deg G S v

def T (S : Finset V) : Finset (Finset V) := (G.cliqueFinset 3).filter (· ⊆ S)

omit [Fintype V] [DecidableEq V] in
lemma A_self (v : V) : A G v v = 0 := by simp [A]
omit [Fintype V] [DecidableEq V] in
lemma A_symm (u v : V) : A G u v = A G v u := by simp [A, G.adj_comm]
omit [Fintype V] [DecidableEq V] in
lemma A_adj {u v : V} (h : G.Adj u v) : A G u v = 1 := by simp [A, h]

omit [Fintype V] in
lemma sum_split {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (f : V → ℕ) :
    ∑ v ∈ S, f v = f x + f y + ∑ v ∈ (S.erase x).erase y, f v := by
  rw [← add_sum_erase S f hx, ← add_sum_erase (S.erase x) f (mem_erase.2 ⟨hxy.symm, hy⟩)]
  ring

omit [Fintype V] in
lemma deg_split {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (v : V) :
    deg G S v = A G v x + A G v y + deg G ((S.erase x).erase y) v := by
  unfold deg; exact sum_split hx hy hxy (A G v)

omit [Fintype V] [DecidableEq V] in
lemma deg_eq_card (S : Finset V) (v : V) : deg G S v = (S.filter (G.Adj v)).card := by
  unfold deg A; rw [Finset.card_filter]

omit [Fintype V] in
lemma P_split {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hadj : G.Adj x y) :
    P G S + 2 = P G ((S.erase x).erase y) + 2 * (deg G S x + deg G S y) := by
  have hd : ∀ v, deg G S v = A G v x + A G v y + deg G ((S.erase x).erase y) v :=
    fun v => deg_split G hx hy hxy v
  have hx' : deg G S x = 1 + deg G ((S.erase x).erase y) x := by
    have := hd x; rw [A_self, A_adj G hadj] at this; omega
  have hy' : deg G S y = 1 + deg G ((S.erase x).erase y) y := by
    have := hd y; rw [A_self, A_adj G hadj.symm] at this; omega
  have e1 : ∑ v ∈ (S.erase x).erase y, A G v x = deg G ((S.erase x).erase y) x := by
    unfold deg; exact sum_congr rfl (fun v _ => A_symm G v x)
  have e2 : ∑ v ∈ (S.erase x).erase y, A G v y = deg G ((S.erase x).erase y) y := by
    unfold deg; exact sum_congr rfl (fun v _ => A_symm G v y)
  have hsum : ∑ v ∈ (S.erase x).erase y, deg G S v = P G ((S.erase x).erase y) +
      (deg G ((S.erase x).erase y) x + deg G ((S.erase x).erase y) y) := by
    rw [Finset.sum_congr rfl (fun v (_ : v ∈ (S.erase x).erase y) => hd v), sum_add_distrib,
      sum_add_distrib, e1, e2]
    unfold P; ring
  have hP : P G S = deg G S x + deg G S y + ∑ v ∈ (S.erase x).erase y, deg G S v := by
    unfold P; exact sum_split hx hy hxy (deg G S)
  rw [hP, hsum]; omega

omit [Fintype V] [DecidableEq V] in
lemma exists_adj {S : Finset V} (h : 0 < P G S) : ∃ x ∈ S, ∃ y ∈ S, G.Adj x y := by
  by_contra hc
  have hc' : ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y := fun x hx y hy hxy => hc ⟨x, hx, y, hy, hxy⟩
  have : P G S = 0 := by
    unfold P
    exact Finset.sum_eq_zero (fun v hv => by
      unfold deg; exact Finset.sum_eq_zero (fun u hu => by simp [A, hc' v hv u hu]))
  omega

omit [Fintype V] in
lemma no_common {S : Finset V} {x y : V} (h : ∀ w ∈ S, ¬ (G.Adj x w ∧ G.Adj y w)) :
    deg G S x + deg G S y ≤ S.card := by
  rw [deg_eq_card, deg_eq_card, ← Finset.card_union_of_disjoint]
  · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  · rw [Finset.disjoint_left]; intro w h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h w h1.1 ⟨h1.2, h2.2⟩

lemma mantel : ∀ s (S : Finset V), S.card = s → 2 * (s ^ 2 / 4 + 1) ≤ P G S →
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro S hS hP
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj G (S := S) (by omega)
  by_cases hc : ∃ w ∈ S, G.Adj x w ∧ G.Adj y w
  · obtain ⟨w, hw, h1, h2⟩ := hc
    exact ⟨x, hx, y, hy, w, hw, hxy, h1, h2⟩
  · have hb := no_common G (fun w hw h => hc ⟨w, hw, h⟩)
    have hne : x ≠ y := G.ne_of_adj hxy
    have hsplit := P_split G hx hy hne hxy
    have hcard : ((S.erase x).erase y).card = s - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hne.symm, hy⟩), card_erase_of_mem hx]; omega
    have h0 : 0 < (S.erase x).card := card_pos.2 ⟨y, mem_erase.2 ⟨hne.symm, hy⟩⟩
    rw [card_erase_of_mem hx] at h0
    obtain ⟨x', hx', y', hy', z', hz', h⟩ := ih (s - 2) (by omega) _ hcard (by
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
      have e : (k + 2) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
      rw [e] at hP
      simp only [Nat.add_sub_cancel]
      omega)
    exact ⟨x', mem_of_mem_erase (mem_of_mem_erase hx'), y', mem_of_mem_erase (mem_of_mem_erase hy'),
      z', mem_of_mem_erase (mem_of_mem_erase hz'), h⟩

lemma T_mono {S S' : Finset V} (h : S' ⊆ S) : T G S' ⊆ T G S := by
  intro t ht; simp only [T, Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.trans h⟩

lemma tri_mem {S : Finset V} {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3 : G.Adj b c) : ({a, b, c} : Finset V) ∈ T G S := by
  simp only [T, Finset.mem_filter, mem_cliqueFinset_iff, is3Clique_triple_iff]
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl <;> assumption

lemma T_step {S : Finset V} {x y w : V} (hx : x ∈ S) (hy : y ∈ S) (hw : w ∈ S)
    (h1 : G.Adj x y) (h2 : G.Adj x w) (h3 : G.Adj y w) :
    (T G ((S.erase x).erase y)).card + 1 ≤ (T G S).card := by
  have hsub : T G ((S.erase x).erase y) ⊂ T G S := by
    refine Finset.ssubset_iff_subset_ne.2
      ⟨T_mono G ((erase_subset _ _).trans (erase_subset _ _)), ?_⟩
    intro heq
    have := tri_mem G hx hy hw h1 h2 h3
    rw [← heq] at this
    simp only [T, Finset.mem_filter] at this
    have hx' := this.2 (by simp : x ∈ ({x, y, w} : Finset V))
    simp at hx'
  exact Finset.card_lt_card hsub

lemma pair_case {s : ℕ}
    (ih : ∀ m < s, ∀ S : Finset V, S.card = m → 2 * (m ^ 2 / 4 + 1) ≤ P G S →
      m / 2 ≤ (T G S).card)
    {S : Finset V} (hS : S.card = s) (hP : 2 * (s ^ 2 / 4 + 1) ≤ P G S) {x y w : V}
    (hx : x ∈ S) (hy : y ∈ S) (hw : w ∈ S) (h1 : G.Adj x y) (h2 : G.Adj x w) (h3 : G.Adj y w)
    (hb : deg G S x + deg G S y ≤ s) : s / 2 ≤ (T G S).card := by
  have hne : x ≠ y := G.ne_of_adj h1
  have hsplit := P_split G hx hy hne h1
  have hcard : ((S.erase x).erase y).card = s - 2 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hne.symm, hy⟩), card_erase_of_mem hx]; omega
  have h0 : 0 < ((S.erase x).erase y).card :=
    card_pos.2 ⟨w, by simp [hw, (G.ne_of_adj h2).symm, (G.ne_of_adj h3).symm]⟩
  have hstep := T_step G hx hy hw h1 h2 h3
  have := ih (s - 2) (by omega) _ hcard (by
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
    have e : (k + 2) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
    rw [e] at hP
    simp only [Nat.add_sub_cancel]
    omega)
  omega

/-- the triangle `{x,y,w}`, `{y,z,w}` or `{x,z,w}` -/
def g (x y z : V) (p : V × Fin 3) : Finset V :=
  ![({x, y, p.1} : Finset V), {y, z, p.1}, {x, z, p.1}] p.2

def idx (x z : V) (t : Finset V) : Fin 3 := if z ∉ t then 0 else if x ∉ t then 1 else 2

omit [Fintype V] in
lemma g_inj {x y z : V} {W : Finset V} (hW : ∀ w ∈ W, w ≠ x ∧ w ≠ y ∧ w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Set.InjOn (g x y z) ↑(W ×ˢ (univ : Finset (Fin 3))) := by
  rintro ⟨w1, i1⟩ h1 ⟨w2, i2⟩ h2 he
  rw [Finset.mem_coe, Finset.mem_product] at h1 h2
  obtain ⟨a1, b1, c1⟩ := hW w1 h1.1
  have hw : w1 = w2 := by
    have : w1 ∈ g x y z (w1, i1) := by fin_cases i1 <;> simp [g]
    rw [he] at this
    fin_cases i2 <;> simp [g, a1, b1, c1] at this <;> exact this
  subst hw
  have hr : ∀ i, idx x z (g x y z (w1, i)) = i := by
    intro i
    fin_cases i <;> simp [idx, g, hxy, hxz, hxz.symm, hyz.symm, a1.symm, c1.symm]
  refine Prod.ext rfl ?_
  calc i1 = idx x z (g x y z (w1, i1)) := (hr i1).symm
    _ = idx x z (g x y z (w1, i2)) := by rw [he]
    _ = i2 := hr i2

lemma triple {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (h1 : G.Adj x y) (h2 : G.Adj x z) (h3 : G.Adj y z) :
    deg G S x + deg G S y + deg G S z ≤ (T G S).card + S.card + 2 := by
  have hxy := G.ne_of_adj h1
  have hxz := G.ne_of_adj h2
  have hyz := G.ne_of_adj h3
  have hz' : z ∈ (S.erase x).erase y := by simp [hz, hyz.symm, hxz.symm]
  obtain ⟨W, hWdef⟩ : ∃ W, W = ((S.erase x).erase y).erase z := ⟨_, rfl⟩
  have hW : ∀ w ∈ W, w ≠ x ∧ w ≠ y ∧ w ≠ z := by
    intro w hw; rw [hWdef] at hw; simp only [mem_erase] at hw
    exact ⟨hw.2.2.1, hw.2.1, hw.1⟩
  have hWS : W ⊆ S := by
    intro w hw; rw [hWdef] at hw; simp only [mem_erase] at hw; exact hw.2.2.2
  have dsplit : ∀ v, deg G S v = A G v x + A G v y + A G v z + ∑ w ∈ W, A G v w := by
    intro v
    rw [deg_split G hx hy hxy v, hWdef]; unfold deg
    rw [← add_sum_erase _ _ hz']; ring
  have c1 : ((S.erase x).erase y).card = S.card - 2 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hxy.symm, hy⟩), card_erase_of_mem hx]; omega
  have c0 := Finset.card_pos.2 ⟨z, hz'⟩
  have hcardW : W.card + 3 = S.card := by rw [hWdef, card_erase_of_mem hz']; omega
  obtain ⟨D, hD⟩ : ∃ D, D = (W ×ˢ (univ : Finset (Fin 3))).filter
      (fun p => g x y z p ∈ G.cliqueFinset 3) := ⟨_, rfl⟩
  have hDsub : insert ({x, y, z} : Finset V) (D.image (g x y z)) ⊆ T G S := by
    intro t ht
    rw [mem_insert, mem_image] at ht
    rcases ht with rfl | ⟨⟨w, i⟩, hp, rfl⟩
    · exact tri_mem G hx hy hz h1 h2 h3
    · rw [hD, mem_filter, mem_product] at hp
      obtain ⟨⟨hpW, -⟩, hpc⟩ := hp
      have hwS : w ∈ S := hWS hpW
      simp only [T, mem_filter]
      refine ⟨hpc, ?_⟩
      fin_cases i <;>
        (intro u hu; simp [g] at hu; rcases hu with rfl | rfl | rfl <;> assumption)
  have hnot : ({x, y, z} : Finset V) ∉ D.image (g x y z) := by
    rw [mem_image]; rintro ⟨⟨w, i⟩, hp, he⟩
    rw [hD, mem_filter, mem_product] at hp
    obtain ⟨a, b, c⟩ := hW w hp.1.1
    have : w ∈ g x y z (w, i) := by fin_cases i <;> simp [g]
    rw [he] at this
    simp [a, b, c] at this
  have hinj : Set.InjOn (g x y z) ↑D := by
    refine Set.InjOn.mono ?_ (g_inj hW hxy hxz hyz)
    rw [hD]; exact Finset.coe_subset.2 (filter_subset _ _)
  have hTD : D.card + 1 ≤ (T G S).card := by
    have := card_le_card hDsub
    rw [card_insert_of_notMem hnot, card_image_of_injOn hinj] at this
    exact this
  have hcardD : D.card = ∑ w ∈ W, ∑ i : Fin 3,
      (if g x y z (w, i) ∈ G.cliqueFinset 3 then 1 else 0) := by
    rw [hD, card_filter, sum_product]
  have hper : ∀ w ∈ W, A G x w + A G y w + A G z w ≤
      (∑ i : Fin 3, (if g x y z (w, i) ∈ G.cliqueFinset 3 then 1 else 0)) + 1 := by
    intro w hw
    rw [Fin.sum_univ_three]
    by_cases ha : G.Adj x w <;> by_cases hb : G.Adj y w <;> by_cases hc : G.Adj z w <;>
      simp [g, A, ha, hb, hc, h1, h2, h3, is3Clique_triple_iff]
  have hsumle : ∑ w ∈ W, (A G x w + A G y w + A G z w) ≤ D.card + W.card := by
    rw [hcardD, card_eq_sum_ones W, ← sum_add_distrib]
    exact sum_le_sum hper
  rw [sum_add_distrib, sum_add_distrib] at hsumle
  rw [dsplit x, dsplit y, dsplit z]
  simp only [A_self, A_adj G h1, A_adj G h2, A_adj G h3, A_adj G h1.symm, A_adj G h2.symm,
    A_adj G h3.symm]
  omega

lemma main : ∀ s (S : Finset V), S.card = s → 2 * (s ^ 2 / 4 + 1) ≤ P G S →
    s / 2 ≤ (T G S).card := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro S hS hP
  obtain ⟨x, hx, y, hy, z, hz, h1, h2, h3⟩ := mantel G s S hS hP
  by_cases hab : deg G S x + deg G S y ≤ s
  · exact pair_case G ih hS hP hx hy hz h1 h2 h3 hab
  by_cases hbc : deg G S y + deg G S z ≤ s
  · exact pair_case G ih hS hP hy hz hx h3 h1.symm h2.symm hbc
  by_cases hac : deg G S x + deg G S z ≤ s
  · exact pair_case G ih hS hP hx hz hy h2 h1 h3.symm hac
  have := triple G hx hy hz h1 h2 h3
  omega

end Rad

namespace Erdos1010

open scoped Classical in
theorem erdos_1010.variants.rademacher : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.edgeFinset.card = n ^ 2 / 4 + 1 → n / 2 ≤ (G.cliqueFinset 3).card := by
  intro n G hG
  have hP : Rad.P G univ = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_eq_twice_card_edges]
    unfold Rad.P
    refine sum_congr rfl (fun v _ => ?_)
    rw [Rad.deg_eq_card, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have hT : Rad.T G univ = G.cliqueFinset 3 := by
    unfold Rad.T; exact filter_true_of_mem (fun t _ => subset_univ t)
  have := Rad.main G n univ (card_fin n) (by rw [hP, hG])
  rwa [hT] at this

end Erdos1010

#print axioms Erdos1010.erdos_1010.variants.rademacher
