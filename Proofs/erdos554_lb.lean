import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring

namespace SimpleGraph

noncomputable def multicolourGraphRamsey {α : Type*} [Fintype α] (k : ℕ) (G : SimpleGraph α) : ℕ :=
  sInf {n : ℕ | ∀ C : TopEdgeLabeling (Fin n) (Fin k), ∃ i, G.IsContained (C.labelGraph i)}

end SimpleGraph

open SimpleGraph

namespace Erdos554

namespace LB

/-- Greedy multicolour Ramsey sequence: from `(k+1)^j` vertices we extract `j` vertices
`f 0, …, f (j-1)` such that the colour of `{f i, f i'}` (`i < i'`) depends only on `i`. -/
lemma seq {V K : Type*} [DecidableEq V] [Fintype K] [DecidableEq K] (col : V → V → K) :
    ∀ (j : ℕ) (S : Finset V), (Fintype.card K + 1) ^ j ≤ S.card →
      ∃ f : Fin j → V, Function.Injective f ∧ (∀ i, f i ∈ S) ∧
        ∃ c : Fin j → K, ∀ i i', i < i' → col (f i) (f i') = c i := by
  intro j
  induction j with
  | zero =>
    intro S _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, Fin.elim0, fun i => i.elim0⟩
  | succ j ih =>
    intro S hS
    have hP : 1 ≤ (Fintype.card K + 1) ^ j := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hexp : (Fintype.card K + 1) ^ (j + 1) =
        Fintype.card K * (Fintype.card K + 1) ^ j + (Fintype.card K + 1) ^ j := by ring
    have hpos : 0 < S.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hK : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨col v v⟩
    have hT : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
    have hlt : (Finset.univ : Finset K).card * ((Fintype.card K + 1) ^ j - 1) <
        (S.erase v).card := by
      rw [Finset.card_univ, hT, Nat.mul_sub_one]
      have hkP : Fintype.card K ≤ Fintype.card K * (Fintype.card K + 1) ^ j :=
        Nat.le_mul_of_pos_right _ hP
      obtain ⟨Q, hQ⟩ : ∃ Q, Fintype.card K * (Fintype.card K + 1) ^ j = Q := ⟨_, rfl⟩
      rw [hQ] at hexp hkP ⊢
      omega
    obtain ⟨a, -, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := col v)
      (fun x _ => Finset.mem_univ (col v x)) hlt
    obtain ⟨f, finj, fmem, c, hc⟩ := ih ((S.erase v).filter (fun x => col v x = a)) (by omega)
    have fmem' : ∀ i, f i ∈ S.erase v ∧ col v (f i) = a := fun i => Finset.mem_filter.mp (fmem i)
    refine ⟨Fin.cons v f, ?_, ?_, Fin.cons a c, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, finj⟩
      rintro ⟨i, hi⟩
      have := (fmem' i).1
      rw [hi] at this
      simp at this
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hv
      · simpa using Finset.mem_of_mem_erase (fmem' i).1
    · intro i i' hii'
      induction i using Fin.cases with
      | zero =>
        induction i' using Fin.cases with
        | zero => exact absurd hii' (lt_irrefl _)
        | succ t => simpa using (fmem' t).2
      | succ s =>
        induction i' using Fin.cases with
        | zero => exact absurd hii' (Fin.not_lt_zero _)
        | succ t => simpa using hc s t (Fin.succ_lt_succ_iff.mp hii')

/-- Every `k`-colouring of a large complete graph has a monochromatic `C_{2n+1}`. -/
lemma ramsey_cycle (n k : ℕ) (hk : 1 ≤ k) : ∃ N, ∀ C : TopEdgeLabeling (Fin N) (Fin k),
    ∃ i, (cycleGraph (2 * n + 1)).IsContained (C.labelGraph i) := by
  refine ⟨(k + 1) ^ (k * (2 * n + 1) + 1), fun C => ?_⟩
  let a0 : Fin k := ⟨0, hk⟩
  let col : Fin ((k + 1) ^ (k * (2 * n + 1) + 1)) → Fin ((k + 1) ^ (k * (2 * n + 1) + 1)) →
      Fin k := fun x y => if h : x ≠ y then C.get x y h else a0
  obtain ⟨f, finj, -, c, hc⟩ := seq col (k * (2 * n + 1) + 1) Finset.univ (by simp)
  have hlt : (Finset.univ : Finset (Fin k)).card * (2 * n) <
      (Finset.univ : Finset (Fin (k * (2 * n + 1) + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have : k * (2 * n + 1) = k * (2 * n) + k := by ring
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := c)
    (fun x _ => Finset.mem_univ (c x)) hlt
  set P := (Finset.univ : Finset (Fin (k * (2 * n + 1) + 1))).filter (fun x => c x = a) with hPdef
  have hP2 : 2 * n + 1 ≤ P.card := ha
  let g : Fin (2 * n + 1) → Fin (k * (2 * n + 1) + 1) :=
    fun x => P.orderEmbOfFin rfl (Fin.castLE hP2 x)
  have ginj : Function.Injective g := fun x y h =>
    Fin.castLE_injective hP2 ((P.orderEmbOfFin rfl).injective h)
  have gmem : ∀ x, c (g x) = a := fun x => by
    have := P.orderEmbOfFin_mem rfl (Fin.castLE hP2 x)
    exact (Finset.mem_filter.mp this).2
  have fginj : Function.Injective (f ∘ g) := finj.comp ginj
  refine ⟨a, ⟨⟨⟨f ∘ g, ?_⟩, fginj⟩⟩⟩
  intro x y hxy
  have hne : x ≠ y := hxy.ne
  have hne' : f (g x) ≠ f (g y) := fginj.ne hne
  show ((C.labelGraph a).Adj (f (g x)) (f (g y)))
  rw [TopEdgeLabeling.labelGraph_adj]
  refine ⟨hne', ?_⟩
  rcases lt_or_gt_of_ne (ginj.ne hne) with h | h
  · have := hc _ _ h
    simp only [col, dif_pos hne'] at this
    exact this.trans (gmem x)
  · have := hc _ _ h
    have hne'' : f (g y) ≠ f (g x) := hne'.symm
    simp only [col, dif_pos hne''] at this
    rw [EdgeLabeling.get_comm]
    exact this.trans (gmem y)

/-! ## Odd cycles -/

lemma adj_succ (n i : ℕ) (h : i + 1 < 2 * n + 1) :
    (cycleGraph (2 * n + 1)).Adj ⟨i + 1, h⟩ ⟨i, by omega⟩ := by
  rw [cycleGraph_adj']
  left
  rw [Fin.sub_val_of_le (Fin.mk_le_mk.mpr (by omega))]
  simp

lemma adj_wrap (n : ℕ) (hn : 1 ≤ n) :
    (cycleGraph (2 * n + 1)).Adj ⟨0, by omega⟩ ⟨2 * n, by omega⟩ := by
  rw [cycleGraph_adj']
  left
  rw [Fin.coe_sub_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))]
  simp

lemma const_of (n : ℕ) (g : Fin (2 * n + 1) → ℕ)
    (hg : ∀ u v, (cycleGraph (2 * n + 1)).Adj u v → g u = g v) :
    ∀ i (h : i < 2 * n + 1), g ⟨i, h⟩ = g ⟨0, by omega⟩ := by
  intro i
  induction i with
  | zero => intro h; rfl
  | succ i ih =>
    intro h
    rw [hg _ _ (adj_succ n i h), ih]

lemma no_parity (n : ℕ) (hn : 1 ≤ n) (g : Fin (2 * n + 1) → ℕ)
    (hg : ∀ u v, (cycleGraph (2 * n + 1)).Adj u v → g u % 2 ≠ g v % 2) : False := by
  have key : ∀ i (h : i < 2 * n + 1), g ⟨i, h⟩ % 2 = (g ⟨0, by omega⟩ + i) % 2 := by
    intro i
    induction i with
    | zero => intro h; rfl
    | succ i ih =>
      intro h
      have h1 := hg _ _ (adj_succ n i h)
      have h2 := ih (by omega)
      omega
  have h1 := hg _ _ (adj_wrap n hn)
  have h2 := key (2 * n) (by omega)
  omega

/-! ## The construction -/

lemma ex (n k' : ℕ) (x y : Fin (n * 2 ^ (k' + 1))) :
    ∃ t, x.val / (2 * n * 2 ^ t) = y.val / (2 * n * 2 ^ t) := by
  refine ⟨k', ?_⟩
  have e : n * 2 ^ (k' + 1) = 2 * n * 2 ^ k' := by ring
  have hx : x.val < 2 * n * 2 ^ k' := lt_of_lt_of_eq x.isLt e
  have hy : y.val < 2 * n * 2 ^ k' := lt_of_lt_of_eq y.isLt e
  rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy]

lemma find_le (n k' : ℕ) (x y : Fin (n * 2 ^ (k' + 1))) : Nat.find (ex n k' x y) ≤ k' :=
  Nat.find_min' _ (by
    have e : n * 2 ^ (k' + 1) = 2 * n * 2 ^ k' := by ring
    have hx : x.val < 2 * n * 2 ^ k' := lt_of_lt_of_eq x.isLt e
    have hy : y.val < 2 * n * 2 ^ k' := lt_of_lt_of_eq y.isLt e
    rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy])

/-- Colour `t` = least level `t` at which `x` and `y` lie in the same block of size `2n·2^t`. -/
noncomputable def C (n k' : ℕ) : TopEdgeLabeling (Fin (n * 2 ^ (k' + 1))) (Fin (k' + 1)) :=
  EdgeLabeling.mk (fun x y _ => ⟨Nat.find (ex n k' x y), Nat.lt_succ_of_le (find_le n k' x y)⟩)
    (by
      intro x y _
      ext
      exact le_antisymm (Nat.find_mono (fun t h => h.symm)) (Nat.find_mono (fun t h => h.symm)))

lemma C_adj (n k' : ℕ) {x y : Fin (n * 2 ^ (k' + 1))} {c : Fin (k' + 1)}
    (h : ((C n k').labelGraph c).Adj x y) : Nat.find (ex n k' x y) = c.val := by
  rw [TopEdgeLabeling.labelGraph_adj] at h
  obtain ⟨H, hH⟩ := h
  rw [← hH]
  rfl

lemma col0 (n k' : ℕ) {x y : Fin (n * 2 ^ (k' + 1))} {c : Fin (k' + 1)}
    (h : ((C n k').labelGraph c).Adj x y) (hc : c.val = 0) :
    x.val / (2 * n) = y.val / (2 * n) := by
  have hs := Nat.find_spec (ex n k' x y)
  rw [C_adj n k' h, hc] at hs
  simpa using hs

lemma colS (n k' s : ℕ) {x y : Fin (n * 2 ^ (k' + 1))} {c : Fin (k' + 1)}
    (h : ((C n k').labelGraph c).Adj x y) (hc : c.val = s + 1) :
    x.val / (2 * n * 2 ^ s) % 2 ≠ y.val / (2 * n * 2 ^ s) % 2 := by
  have hf : Nat.find (ex n k' x y) = s + 1 := (C_adj n k' h).trans hc
  have hs := Nat.find_spec (ex n k' x y)
  rw [hf] at hs
  have hmin := Nat.find_min (ex n k' x y) (show s < Nat.find (ex n k' x y) by omega)
  have e : 2 * n * 2 ^ (s + 1) = 2 * n * 2 ^ s * 2 := by ring
  have h1 : ∀ z : ℕ, z / (2 * n * 2 ^ (s + 1)) = z / (2 * n * 2 ^ s) / 2 := fun z => by
    rw [Nat.div_div_eq_div_mul, e]
  rw [h1, h1] at hs
  omega

lemma no_mono (n k' : ℕ) (hn : 1 ≤ n) (c : Fin (k' + 1)) :
    ¬ (cycleGraph (2 * n + 1)).IsContained ((C n k').labelGraph c) := by
  rintro ⟨φ⟩
  have hadj : ∀ u v, (cycleGraph (2 * n + 1)).Adj u v →
      ((C n k').labelGraph c).Adj (φ u) (φ v) := fun u v h => φ.toHom.map_adj h
  rcases hc : c.val with _ | s
  · have hconst := const_of n (fun u => (φ u).val / (2 * n))
      (fun u v h => col0 n k' (hadj u v h) hc)
    let m : Fin (2 * n + 1) → Fin (2 * n) := fun u => ⟨(φ u).val % (2 * n), Nat.mod_lt _ (by omega)⟩
    have minj : Function.Injective m := by
      intro u v huv
      apply φ.injective
      have h1 : (φ u).val % (2 * n) = (φ v).val % (2 * n) := congrArg Fin.val huv
      have h2 := hconst u.val u.isLt
      have h3 := hconst v.val v.isLt
      simp only [Fin.eta] at h2 h3
      apply Fin.ext
      show (φ u).val = (φ v).val
      rw [← Nat.div_add_mod (φ u).val (2 * n), ← Nat.div_add_mod (φ v).val (2 * n), h1, h2, h3]
    have := Fintype.card_le_of_injective m minj
    simp at this
  · exact no_parity n hn (fun u => (φ u).val / (2 * n * 2 ^ s))
      (fun u v h => colS n k' s (hadj u v h) hc)

lemma pull_copy {m N k : ℕ} (hle : m ≤ N) (C : TopEdgeLabeling (Fin N) (Fin k)) (i : Fin k) :
    ((C.pullback (Fin.castLEEmb hle)).labelGraph i).IsContained (C.labelGraph i) := by
  refine ⟨⟨⟨Fin.castLEEmb hle, ?_⟩, (Fin.castLEEmb hle).injective⟩⟩
  intro x y hxy
  rw [TopEdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨H, hH⟩ := hxy
  exact ⟨(Fin.castLEEmb hle).injective.ne H, hH⟩

end LB

theorem erdos_554.variants.lower_bound :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      n * 2 ^ k + 1 ≤ multicolourGraphRamsey k (cycleGraph (2 * n + 1)) := by
  intro n hn k hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨N0, hN0⟩ := LB.ramsey_cycle n (k' + 1) hk
  unfold multicolourGraphRamsey
  refine le_csInf ⟨N0, hN0⟩ ?_
  intro m hm
  rcases Nat.lt_or_ge m (n * 2 ^ (k' + 1) + 1) with hlt | hge
  · exfalso
    have hle : m ≤ n * 2 ^ (k' + 1) := by omega
    obtain ⟨i, hi⟩ := hm ((LB.C n k').pullback (Fin.castLEEmb hle))
    exact LB.no_mono n k' hn i (hi.trans (LB.pull_copy hle _ i))
  · exact hge

end Erdos554

#print axioms Erdos554.erdos_554.variants.lower_bound
