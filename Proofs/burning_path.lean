import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

-- Proof of BurningNumberConjecture.burning_number_conjecture.variants.path
-- (Paper/BurningNumberConjecture.lean:85). Definitions restated verbatim.

open Finset

namespace BurningNumberConjecture

variable {V : Type*}

def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

namespace PathAux

open SimpleGraph

lemma walk_ge {n : ℕ} : ∀ {u v : Fin n} (p : (pathGraph n).Walk u v),
    u.val ≤ v.val + p.length ∧ v.val ≤ u.val + p.length := by
  intro u v p
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [pathGraph_adj] at h
    simp only [Walk.length_cons]
    omega

lemma dist_ge {n : ℕ} (u v : Fin n) :
    u.val ≤ v.val + (pathGraph n).dist u v ∧ v.val ≤ u.val + (pathGraph n).dist u v := by
  obtain ⟨p, hp⟩ := (pathGraph_preconnected n u v).exists_walk_length_eq_dist
  rw [← hp]
  exact walk_ge p

lemma walk_up (n d : ℕ) : ∀ (u v : Fin n), v.val = u.val + d →
    ∃ p : (pathGraph n).Walk u v, p.length = d := by
  induction d with
  | zero =>
    intro u v h
    have : u = v := Fin.ext (by omega)
    subst this
    exact ⟨Walk.nil, rfl⟩
  | succ d ih =>
    intro u v h
    obtain ⟨p, hp⟩ := ih u ⟨u.val + d, by omega⟩ rfl
    have hadj : (pathGraph n).Adj ⟨u.val + d, by omega⟩ v :=
      pathGraph_adj.2 (Or.inl (by simp only; omega))
    exact ⟨p.concat hadj, by rw [Walk.length_concat, hp]⟩

lemma close {n : ℕ} (c v : Fin n) (r : ℕ) (h1 : c.val ≤ v.val + r) (h2 : v.val ≤ c.val + r) :
    (pathGraph n).dist c v ≤ r := by
  rcases le_total c.val v.val with h | h
  · obtain ⟨p, hp⟩ := walk_up n (v.val - c.val) c v (by omega)
    exact (dist_le p).trans (by omega)
  · obtain ⟨p, hp⟩ := walk_up n (c.val - v.val) v c (by omega)
    rw [dist_comm]
    exact (dist_le p).trans (by omega)

lemma ball_card {n : ℕ} (c : Fin n) (r : ℕ) :
    #(univ.filter fun v => (pathGraph n).dist c v ≤ r) ≤ 2 * r + 1 := by
  calc #(univ.filter fun v => (pathGraph n).dist c v ≤ r)
      ≤ #(Icc (c.val - r) (c.val + r)) := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro v hv
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          have := dist_ge c v
          simp only [Finset.mem_coe, Finset.mem_Icc]
          omega
        · intro a _ b _ h
          exact Fin.ext h
    _ ≤ 2 * r + 1 := by rw [Nat.card_Icc]; omega

lemma sum_odd (k : ℕ) : ∑ i ∈ range k, (2 * (k - 1 - i) + 1) = k * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ']
    have h : ∑ i ∈ range k, (2 * (k + 1 - 1 - (i + 1)) + 1) =
        ∑ i ∈ range k, (2 * (k - 1 - i) + 1) :=
      sum_congr rfl (fun i _ => by omega)
    rw [h, ih]
    have e : k + 1 - 1 - 0 = k := by omega
    rw [e]
    ring

lemma count_bound (n k : ℕ) (x : Fin k → Fin n) (hx : IsBurningSequence (pathGraph n) x) :
    n ≤ k * k := by
  classical
  let ball : Fin k → Finset (Fin n) :=
    fun i => univ.filter (fun v => (pathGraph n).dist (x i) v ≤ k - 1 - i)
  have h1 : (univ : Finset (Fin n)) ⊆ univ.biUnion ball := by
    intro v _
    obtain ⟨i, _, hi⟩ := hx v
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, by omega⟩⟩
  have h2 : ∀ i, #(ball i) ≤ 2 * (k - 1 - i) + 1 := fun i => ball_card (x i) _
  calc n = #(univ : Finset (Fin n)) := by simp
    _ ≤ #(univ.biUnion ball) := card_le_card h1
    _ ≤ ∑ i, #(ball i) := card_biUnion_le
    _ ≤ ∑ i : Fin k, (2 * (k - 1 - (i : ℕ)) + 1) := sum_le_sum fun i _ => h2 i
    _ = ∑ i ∈ range k, (2 * (k - 1 - i) + 1) :=
        Fin.sum_univ_eq_sum_range (fun i => 2 * (k - 1 - i) + 1) k
    _ = k * k := sum_odd k

lemma burn_exists (n k : ℕ) (hn : 1 ≤ n) (hk : n ≤ k * k) :
    ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
  refine ⟨fun i => ⟨min (k * k - (k - 1 - i + 1) * (k - 1 - i + 1) + (k - 1 - i)) (n - 1),
    by omega⟩, fun v => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = k * k - v.val - 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt w := ⟨_, rfl⟩
  have hs1 : s * s ≤ w := hs ▸ Nat.sqrt_le w
  have hs2 : w < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt w
  have hv := v.isLt
  have hsk : s < k := by
    by_contra h
    have := Nat.mul_le_mul (Nat.le_of_not_lt h) (Nat.le_of_not_lt h)
    omega
  have hA : (s + 1) * (s + 1) ≤ k * k := Nat.mul_le_mul hsk hsk
  have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
  refine ⟨⟨k - 1 - s, by omega⟩, pathGraph_preconnected n _ _, ?_⟩
  have e : k - 1 - (k - 1 - s) = s := by omega
  dsimp only
  refine lt_of_le_of_lt (Nat.add_le_add_right (close _ v s ?_ ?_) _) (by omega)
  · dsimp only; rw [e]; omega
  · dsimp only; rw [e]; omega

lemma ceil_sq (n : ℕ) : n ≤ ⌈Real.sqrt n⌉₊ * ⌈Real.sqrt n⌉₊ := by
  have h := Nat.le_ceil (Real.sqrt (n : ℝ))
  have h0 := Real.sqrt_nonneg (n : ℝ)
  have : (n : ℝ) ≤ (⌈Real.sqrt n⌉₊ : ℝ) * ⌈Real.sqrt n⌉₊ := by
    calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
      _ ≤ _ := mul_self_le_mul_self h0 h
  exact_mod_cast this

lemma ceil_le_of (n k : ℕ) (h : n ≤ k * k) : ⌈Real.sqrt n⌉₊ ≤ k := by
  rw [Nat.ceil_le]
  have h' : (n : ℝ) ≤ (k : ℝ) * k := by exact_mod_cast h
  calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((k : ℝ) * k) := Real.sqrt_le_sqrt h'
    _ = k := Real.sqrt_mul_self (Nat.cast_nonneg k)

end PathAux

theorem burning_number_conjecture.variants.path (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) = ⌈Real.sqrt n⌉₊ := by
  have hmem : ⌈Real.sqrt n⌉₊ ∈ {k | ∃ x : Fin k → Fin n,
      IsBurningSequence (SimpleGraph.pathGraph n) x} :=
    PathAux.burn_exists n _ hn (PathAux.ceil_sq n)
  unfold burningNumber
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · refine le_csInf ⟨_, hmem⟩ (fun k hk => ?_)
    obtain ⟨x, hx⟩ := hk
    exact PathAux.ceil_le_of n k (PathAux.count_bound n k x hx)

end BurningNumberConjecture

#print axioms BurningNumberConjecture.burning_number_conjecture.variants.path
